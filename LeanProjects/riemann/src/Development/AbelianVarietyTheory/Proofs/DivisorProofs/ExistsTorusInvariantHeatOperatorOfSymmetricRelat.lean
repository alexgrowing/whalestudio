import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPreservesRaynaudTorusWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusWeightScalarZeroCharacterEqOneStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatGlue

section Ring

variable {Ω : Type} [CommRing Ω]

def IsDer (d : Ω → Ω) : Prop := (∀ a b, d (a + b) = d a + d b) ∧ ∀ a b, d (a * b) = a * d b + b * d a

theorem IsDer.map_one {d : Ω → Ω} (h : IsDer d) : d 1 = 0 := by
  have := h.2 1 1
  rw [_root_.mul_one, _root_.one_mul] at this
  exact left_eq_add.1 this

theorem IsDer.map_zero {d : Ω → Ω} (h : IsDer d) : d 0 = 0 := by
  have := h.1 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem IsDer.map_natCast {d : Ω → Ω} (h : IsDer d) (k : ℕ) : d k = 0 := by
  induction k with
  | zero => simpa using h.map_zero
  | succ k ih => rw [Nat.cast_succ, h.1, ih, h.map_one, add_zero]

theorem IsDer.map_neg {d : Ω → Ω} (h : IsDer d) (a : Ω) : d (-a) = -d a := by
  have := h.1 a (-a)
  rw [add_neg_cancel, h.map_zero] at this
  linear_combination -this

theorem IsDer.map_sub {d : Ω → Ω} (h : IsDer d) (a b : Ω) : d (a - b) = d a - d b := by
  rw [sub_eq_add_neg, h.1, h.map_neg, ← sub_eq_add_neg]

theorem IsDer.map_sum {d : Ω → Ω} (h : IsDer d) {β : Type} (s : Finset β) (f : β → Ω) :
    d (∑ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem IsDer.pow_mul {d : Ω → Ω} (h : IsDer d) {g gi : Ω} (hg : g * gi = 1) (k : ℕ) (f : Ω) :
    d (g ^ k * f) = g ^ k * (d f + k * (d g * gi) * f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', _root_.mul_assoc, h.2, ih]
    push_cast
    linear_combination (-(g ^ k * f * d g)) * hg

theorem IsDer.dlog_mul {d : Ω → Ω} (h : IsDer d) {a ai b bi c ci : Ω} (ha : a * ai = 1) (hb : b * bi = 1)
    (hc : c * ci = 1) (e : a * b = c) : d c * ci = d a * ai + d b * bi := by
  subst e
  have eci : ci = ai * bi := by
    linear_combination (-ci * b * bi) * ha - ci * hb + ai * bi * hc
  rw [h.2, eci]
  linear_combination (d b * bi) * ha + (d a * ai) * hb

theorem ringOp_conj {n : ℕ} {d : Ω → Ω} {dd : Fin n → Ω → Ω} (hd : IsDer d) (hdd : ∀ a, IsDer (dd a))
    {Θ : Matrix (Fin n) (Fin n) Ω} (hΘ : ∀ a b, Θ a b = Θ b a) (u : Fin n → Ω) (p p' : Ω) {g gi : Ω} (hg : g * gi = 1)
    (k : ℕ) (f : Ω) :
    ringOp d dd Θ u p p' k (g ^ k * f) =
      g ^ k * (ringOp d dd Θ u p p' k f - 2 * k * ∑ a, ∑ b, Θ a b * (dd b g * gi) * dd a f +
        (k : Ω) ^ 2 * (2 * (d g * gi) - ∑ a, ∑ b, Θ a b * (dd a g * gi) * (dd b g * gi)) * f +
        k * (2 * ∑ a, u a * (dd a g * gi) - ∑ a, ∑ b, Θ a b * dd a (dd b g * gi)) * f) := by
  have e1 : ∀ a b, Θ a b * dd a (dd b (g ^ k * f)) = g ^ k * (Θ a b * dd a (dd b f)) +
      g ^ k * k * (Θ a b * (dd b g * gi) * dd a f) + g ^ k * k * (Θ a b * (dd a g * gi) * dd b f) +
      g ^ k * k * f * (Θ a b * dd a (dd b g * gi)) + g ^ k * k ^ 2 * f * (Θ a b * (dd a g * gi) * (dd b g * gi)) := by
    intro a b
    rw [(hdd b).pow_mul hg, (hdd a).pow_mul hg, (hdd a).1, (hdd a).2 (k * (dd b g * gi)), (hdd a).2 k,
      (hdd a).map_natCast]
    ring
  have e2 : ∑ a, ∑ b, Θ a b * (dd a g * gi) * dd b f = ∑ a, ∑ b, Θ a b * (dd b g * gi) * dd a f := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hΘ]
  have e3 : ∀ a, u a * dd a (g ^ k * f) = g ^ k * (u a * dd a f) + g ^ k * k * f * (u a * (dd a g * gi)) := by
    intro a
    rw [(hdd a).pow_mul hg]; ring
  unfold ringOp
  simp only [e1, e3, Finset.sum_add_distrib, ← Finset.mul_sum, e2, hd.pow_mul hg]
  ring

theorem quad_add {n : ℕ} {Θ : Fin n → Fin n → Ω} (hΘ : ∀ a b, Θ a b = Θ b a) (x y : Fin n → Ω) :
    ∑ a, ∑ b, Θ a b * (x a + y a) * (x b + y b) =
      ∑ a, ∑ b, Θ a b * x a * x b + ∑ a, ∑ b, Θ a b * y a * y b + 2 * ∑ a, ∑ b, Θ a b * x b * y a := by
  have e : ∑ a, ∑ b, Θ a b * x a * y b = ∑ a, ∑ b, Θ a b * x b * y a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hΘ]
  have e' : ∀ a b, Θ a b * (x a + y a) * (x b + y b) =
      Θ a b * x a * x b + Θ a b * y a * y b + Θ a b * x a * y b + Θ a b * x b * y a := fun a b => by ring
  simp only [e', Finset.sum_add_distrib, e]
  ring

end Ring

end GlobalTheory.HeatGlue

namespace GlobalTheory.HeatGlue

open GlobalTheory.KS

section Sch

theorem isDer_of_isField {Z : Scheme.{0}} {W O : Z.Opens} {d : Fld Z} (h : IsField W d) (hO : O ≤ W) : IsDer (d O) :=
  ⟨h.1 O hO, h.2.1 O hO⟩

theorem field_rsT {Z : Scheme.{0}} {W O O' : Z.Opens} {d : Fld Z} (h : IsField W d) (hO : O ≤ W) (h' : O' ≤ O)
    (f : Γ(Z, O)) : d O' (rsT f O') = rsT (d O f) O' := by
  rw [rsT_of_le h', rsT_of_le h']
  exact h.2.2 O O' h' hO f

variable {R : Type} [CommRing R]

theorem constFn_add {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) (a b : R) :
    constFn p O (a + b) = constFn p O a + constFn p O b := by simp [constFn]

theorem constFn_mul {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) (a b : R) :
    constFn p O (a * b) = constFn p O a * constFn p O b := by simp [constFn]

theorem constFn_neg {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) (a : R) :
    constFn p O (-a) = -constFn p O a := by simp [constFn]

theorem constFn_one {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) : constFn p O 1 = 1 := by simp [constFn]

theorem constFn_two {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) : constFn p O 2 = 2 := by
  rw [show (2 : R) = 1 + 1 by norm_num, constFn_add, constFn_one]; norm_num

theorem valR_pbT {A : Type} [CommRing A] {Z X : Scheme.{0}} (a : Sp A ⟶ Z) (p : Z ⟶ X) {O₀ : X.Opens} {O : Z.Opens}
    (hO : O ≤ p ⁻¹ᵁ O₀) (ha : ⊤ ≤ a ⁻¹ᵁ O) (s : Γ(X, O₀)) : valR a O (pbT p s O) = valR (a ≫ p) O₀ s := by
  have ha' : ⊤ ≤ (a ≫ p) ⁻¹ᵁ O₀ := ha.trans (a.preimage_mono hO)
  rw [valR, dif_pos ha, valR, dif_pos ha', pbT_of_le p hO, ← Scheme.Hom.appLE_comp_appLE a p O₀ O ⊤ hO ha]
  rfl

theorem constFn_eq_pbT {Z : Scheme.{0}} (p : Z ⟶ Sp R) (O : Z.Opens) (r : R) :
    constFn p O r = pbT p ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) O := by
  rw [pbT_of_le p (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial)]; rfl

theorem valR_spMap {S : Type} [CommRing S] (φ : R →+* S) (r : R) :
    valR (spMap φ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = φ r := by
  rw [valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from fun _ _ => trivial)]
  have e := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply, CommRingCat.hom_ofHom] at e
  rw [← e]
  rfl

theorem valR_constFn {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) (p : Z ⟶ Sp R) (φ : R →+* A)
    (hp : a ≫ p = spMap φ) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O) (r : R) : valR a O (constFn p O r) = φ r := by
  rw [constFn_eq_pbT, valR_pbT a p (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) ha, hp, valR_spMap]

theorem valR_mul {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem valR_add {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add]

theorem valR_sub {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f - g) = valR a O f - valR a O g := by
  simp only [valR, dif_pos ha, map_sub]

theorem valR_one {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O) :
    valR a O (1 : Γ(Z, O)) = 1 := by
  simp only [valR, dif_pos ha, map_one]

theorem valR_zero {A : Type} [CommRing A] {Z : Scheme.{0}} (a : Sp A ⟶ Z) {O : Z.Opens} :
    valR a O (0 : Γ(Z, O)) = 0 := by
  unfold valR; split_ifs <;> simp

end Sch

end GlobalTheory.HeatGlue

namespace GlobalTheory.HeatGlue

open GlobalTheory.KS

section Wt

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

variable {Y}

theorem isWt_add {α : Q.X} {W : Y.H.left.Opens} {f g : Γ(Y.H.left, W)} (hf : IsWt Y α W f) (hg : IsWt Y α W g) :
    IsWt Y α W (f + g) := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  rw [valR_add a' h2, valR_add a h1, hf S φ x x' c a a' ha ha' h1 h2 hq hc, hg S φ x x' c a a' ha ha' h1 h2 hq hc]
  ring

theorem isWt_sub {α : Q.X} {W : Y.H.left.Opens} {f g : Γ(Y.H.left, W)} (hf : IsWt Y α W f) (hg : IsWt Y α W g) :
    IsWt Y α W (f - g) := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  rw [valR_sub a' h2, valR_sub a h1, hf S φ x x' c a a' ha ha' h1 h2 hq hc, hg S φ x x' c a a' ha ha' h1 h2 hq hc]
  ring

theorem isWt_zero (α : Q.X) (W : Y.H.left.Opens) : IsWt Y α W 0 := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  rw [valR_zero, valR_zero, mul_zero]

theorem isWt_neg {α : Q.X} {W : Y.H.left.Opens} {f : Γ(Y.H.left, W)} (hf : IsWt Y α W f) : IsWt Y α W (-f) := by
  have := isWt_sub (isWt_zero α W) hf
  rwa [zero_sub] at this

theorem isWt_sum {α : Q.X} {W : Y.H.left.Opens} {β : Type} (s : Finset β) (f : β → Γ(Y.H.left, W))
    (hf : ∀ b ∈ s, IsWt Y α W (f b)) : IsWt Y α W (∑ b ∈ s, f b) :=
  Finset.sum_induction f (IsWt Y α W) (fun _ _ => isWt_add) (isWt_zero α W) hf

theorem isWt_constFn_mul {α : Q.X} {W : Y.H.left.Opens} {f : Γ(Y.H.left, W)} (hf : IsWt Y α W f) (r : R) :
    IsWt Y α W (constFn Y.H.hom W r * f) := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  have e : ∀ (z : Over.mk (spMap φ) ⟶ Y.H) (b : Sp S ⟶ Y.H.left), b = z.left → ⊤ ≤ b ⁻¹ᵁ W →
      valR b W (constFn Y.H.hom W r) = φ r := fun z b hb hW => by
    subst hb; exact valR_constFn z.left Y.H.hom φ (Over.w z) hW r
  rw [valR_mul a' h2, valR_mul a h1, e x' a' ha' h2, e x a ha h1, hf S φ x x' c a a' ha ha' h1 h2 hq hc]
  ring

theorem isWt_zero_mul {W : Y.H.left.Opens} {f g : Γ(Y.H.left, W)} (hf : IsWt Y 0 W f) (hg : IsWt Y 0 W g) :
    IsWt Y 0 W (f * g) := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  have h0 : c 0 = 1 := GlobalTheory.T.torusWeightScalar_zeroCharacter_eq_one Y S φ x x' c hq hc
  rw [valR_mul a' h2, valR_mul a h1, hf S φ x x' c a a' ha ha' h1 h2 hq hc, hg S φ x x' c a a' ha ha' h1 h2 hq hc, h0]
  simp

theorem isWt_zero_constFn (W : Y.H.left.Opens) (r : R) : IsWt Y 0 W (constFn Y.H.hom W r) := by
  have := isWt_constFn_mul (Y := Y) (α := 0) (W := W) (f := 1) ?_ r
  · rwa [_root_.mul_one] at this
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  have h0 : c 0 = 1 := GlobalTheory.T.torusWeightScalar_zeroCharacter_eq_one Y S φ x x' c hq hc
  rw [h0, valR_one a' h2, valR_one a h1]; simp

theorem isWt_zero_pbT {V : Q.P.A.left.Opens} (s : Γ(Q.P.A.left, V)) {W : Y.H.left.Opens}
    (hW : W ≤ Y.q.left ⁻¹ᵁ V) : IsWt Y 0 W (pbT Y.q.left s W) := by
  intro S _ φ x x' c a a' ha ha' h1 h2 hq hc
  have h0 : c 0 = 1 := GlobalTheory.T.torusWeightScalar_zeroCharacter_eq_one Y S φ x x' c hq hc
  have e : a' ≫ Y.q.left = a ≫ Y.q.left := by
    subst ha ha'
    have := congrArg CommaMorphism.left hq
    simpa using this
  rw [valR_pbT a' Y.q.left hW h2, valR_pbT a Y.q.left hW h1, e, h0]
  simp

theorem isWt_inv {v : TanM (𝟙 (Sp R)) Y.H} {dd : Fld Y.H.left} (h : IsInv Y.H v dd) {α : Q.X} {W : Y.H.left.Opens}
    {f : Γ(Y.H.left, W)} (hf : IsWt Y α W f) : IsWt Y α W (dd W f) :=
  GlobalTheory.T.invariantVectorField_preserves_raynaudTorusWeight Y v dd h α W f hf

end Wt

end GlobalTheory.HeatGlue

namespace GlobalTheory.HeatGlue

open GlobalTheory.KS

section Dlg

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {X : Scheme.{0}} (m : G.left ⟶ X)
  (L : LB X)

theorem pbT_unit' {Z : Scheme.{0}} (m : Z ⟶ X) {V : X.Opens} (w : Γ(X, V)ˣ) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ V) :
    pbT m w.val O * pbT m w⁻¹.val O = 1 := by
  rw [← pbT_mul, Units.mul_inv, pbT_one m h]

theorem rsT_dlg {δ : Fld G.left} {W : G.left.Opens} (hδ : IsField W δ) (i i' : L.ι) {O₁ O : G.left.Opens}
    (h1 : O₁ ≤ W) (h : O ≤ O₁) (hm : O₁ ≤ m ⁻¹ᵁ (L.U i ⊓ L.U i')) :
    rsT (dlg G m L δ i i' O₁) O = dlg G m L δ i i' O := by
  unfold dlg
  rw [rsT_mul, ← field_rsT hδ h1 h, rsT_pbT m hm h, rsT_pbT m hm h]

theorem pbT_cocycle (hL : L.IsLB) {Z : Scheme.{0}} (m : Z ⟶ X) (i j k : L.ι) {O : Z.Opens}
    (hO : O ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k)) :
    pbT m (L.g i j).val O * pbT m (L.g j k).val O = pbT m (L.g i k).val O := by
  have e := congrArg (fun u : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => pbT m u.val O) (hL.cocycle i j k)
  simp only [Units.val_mul, pbT_mul] at e
  have r : ∀ {V V' : X.Opens} (h : V' ≤ V) (u : Γ(X, V)ˣ), O ≤ m ⁻¹ᵁ V' →
      pbT m (ReciprocityTheory.ChartRestriction.G.Semi.res h u).val O = pbT m u.val O := fun h u hO' => by
    show pbT m (resG X h u.val) O = _
    rw [← rsT_of_le h, pbT_rsT m h hO']
  rw [r _ _ hO, r _ _ hO, r _ _ hO] at e
  exact e

theorem dlg_cocycle (hL : L.IsLB) {δ : Fld G.left} (i j k : L.ι) {O : G.left.Opens} (hδ : IsDer (δ O))
    (hO : O ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k)) :
    dlg G m L δ i k O = dlg G m L δ i j O + dlg G m L δ j k O := by
  have h1 : O ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) := hO.trans (m.preimage_mono inf_le_left)
  have h2 : O ≤ m ⁻¹ᵁ (L.U j ⊓ L.U k) := hO.trans (m.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  have h3 : O ≤ m ⁻¹ᵁ (L.U i ⊓ L.U k) := hO.trans (m.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  exact hδ.dlog_mul (pbT_unit' m _ h1) (pbT_unit' m _ h2) (pbT_unit' m _ h3) (pbT_cocycle L hL m i j k hO)

end Dlg

end GlobalTheory.HeatGlue

namespace GlobalTheory.HeatGlue

open GlobalTheory.KS

theorem resG_constFn {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) {W W' : Z.Opens} (h : W' ≤ W) (r : R) :
    resG Z h (constFn p W r) = constFn p W' r := by
  rw [← rsT_of_le h, rsT_constFn p h]

theorem exists_basic_heat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (Θ : Matrix (Fin n) (Fin n) R) (J : Type)
    (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ → ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) →
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) →
    (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) →
    (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) →
    ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D Θ J V j d hΘ hV hVL hlift hdw hKS hH1
  have hL : Dd.toPre.P.L.IsLB := Dd.toPre.P.isLB
  have hUL : ∀ i, Y.q.left ⁻¹ᵁ V i ≤ Y.q.left ⁻¹ᵁ Dd.toPre.P.L.U (j i) := fun i => Y.q.left.preimage_mono (hVL i)
  have hddF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hdF : ∀ i, IsField (Y.q.left ⁻¹ᵁ V i) (d i) := fun i => (hlift i).1
  have hdd : ∀ a (W : Y.H.left.Opens), IsDer (dd a W) := fun a W => isDer_of_isField (hddF a) le_top
  have hm2 : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' →
      W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) := fun i i' W hW =>
    le_inf (hW.trans (inf_le_left.trans (hUL i))) (hW.trans (inf_le_right.trans (hUL i')))
  have hm3 : ∀ i i' i'' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'' →
      W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i') ⊓ Dd.toPre.P.L.U (j i'')) := fun i i' i'' W hW =>
    le_inf (le_inf (hW.trans (inf_le_left.trans (inf_le_left.trans (hUL i))))
      (hW.trans (inf_le_left.trans (inf_le_right.trans (hUL i'))))) (hW.trans (inf_le_right.trans (hUL i'')))

  have h2 : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]; norm_num
  have hc2 : ∀ W : Y.H.left.Opens, 2 * constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) = 1 := fun W => by
    rw [← constFn_two Y.H.hom W, ← constFn_mul, h2, constFn_one]
  have hs : ∀ (W : Y.H.left.Opens) a b, constFn Y.H.hom W (Θ a b) = constFn Y.H.hom W (Θ b a) := fun W a b => by
    rw [show Θ a b = Θᵀ b a from rfl, hΘ]

  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → J → J → ∀ W : Y.H.left.Opens, Γ(Y.H.left, W),
      ∀ b i i' W, φ b i i' W = dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W := ⟨_, fun _ _ _ _ => rfl⟩
  have rφ : ∀ b i i' (W₁ W : Y.H.left.Opens), W₁ ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → W ≤ W₁ →
      rsT (φ b i i' W₁) W = φ b i i' W := fun b i i' W₁ W h1 h => by
    rw [hφ, hφ]; exact rsT_dlg Y.H Y.q.left _ (hddF b) _ _ le_top h (hm2 i i' W₁ h1)
  have cφ : ∀ b i i' i'' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'' →
      φ b i i'' W = φ b i i' W + φ b i' i'' W := fun b i i' i'' W hW => by
    rw [hφ, hφ, hφ]; exact dlg_cocycle Y.H Y.q.left _ hL _ _ _ (hdd b W) (hm3 i i' i'' W hW)
  have ks : ∀ i i' i'' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' →
      dlg Y.H Y.q.left Dd.toPre.P.L (d i) (j i') (j i'') W = dlg Y.H Y.q.left Dd.toPre.P.L (d i') (j i') (j i'') W +
        ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * φ b i i' W * φ a i' i'' W := fun i i' i'' W hW => by
    unfold dlg
    rw [← sub_eq_iff_eq_add', ← sub_mul, hKS i i' W hW, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hφ, hφ]; unfold dlg; ring

  obtain ⟨z₁, hz₁⟩ : ∃ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), ∀ i i', z i i' =
      -(constFn Y.H.hom (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (algebraMap ℚ R (1 / 2)) *
        ∑ a, ∑ b, constFn Y.H.hom (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (Θ a b) *
          dd a (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (φ b i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), ∀ i i', z i i' =
      dlg Y.H Y.q.left Dd.toPre.P.L (d i) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') -
        constFn Y.H.hom (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (algebraMap ℚ R (1 / 2)) *
        ∑ a, ∑ b, constFn Y.H.hom (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (Θ a b) *
          φ a i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') * φ b i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') :=
    ⟨_, fun _ _ => rfl⟩
  have rz₁ : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → rsT (z₁ i i') W =
      -(constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) * ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dd a W (φ b i i' W)) := by
    intro i i' W hW
    have e : ∀ a b, rsT (dd a (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (φ b i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) W =
        dd a W (φ b i i' W) := fun a b => by
      rw [← field_rsT (hddF a) le_top hW, rφ b i i' _ W le_rfl hW]
    rw [hz₁]
    simp only [rsT_neg, rsT_mul, rsT_sum, rsT_constFn _ hW, e]
  have rz₂ : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → rsT (z₂ i i') W =
      dlg Y.H Y.q.left Dd.toPre.P.L (d i) (j i) (j i') W - constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) *
        ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * φ a i i' W * φ b i i' W := by
    intro i i' W hW
    have e : ∀ b, rsT (φ b i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) W = φ b i i' W := fun b =>
      rφ b i i' _ W le_rfl hW
    rw [hz₂]
    simp only [rsT_sub, rsT_mul, rsT_sum, rsT_constFn _ hW, e]
    rw [rsT_dlg Y.H Y.q.left _ (hdF i) _ _ inf_le_left hW (hm2 i i' _ le_rfl)]

  have tri : ∀ i i' i'', (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'' ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') ∧
      (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'' ≤ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') ∧
      (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'' ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'') :=
    fun _ _ _ => ⟨inf_le_left, le_inf (inf_le_left.trans inf_le_right) inf_le_right,
      le_inf (inf_le_left.trans inf_le_left) inf_le_right⟩
  have coc₁ : IsCoc _ z₁ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₁ i i' _ t1, rz₁ i' i'' _ t2, rz₁ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e, (hdd _ _).1, mul_add, Finset.sum_add_distrib]
    ring
  have coc₂ : IsCoc _ z₂ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₂ i i' _ t1, rz₂ i' i'' _ t2, rz₂ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e]
    rw [dlg_cocycle Y.H Y.q.left _ hL (j i) (j i') (j i'')
      (isDer_of_isField (hdF i) (t1.trans inf_le_left)) (hm3 i i' i'' _ le_rfl), ks i i' i'' _ t1,
      quad_add (hs _) (fun a => φ a i i' _) (fun a => φ a i' i'' _)]
    linear_combination (∑ a, ∑ b, constFn Y.H.hom (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') (Θ a b) *
      φ b i i' _ * φ a i' i'' _) * hc2 _

  have wφ : ∀ b i i', IsWt Y 0 (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (φ b i i' (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) := by
    intro b i i'
    rw [hφ]
    exact isWt_zero_mul (isWt_inv (hinv b) (isWt_zero_pbT _ (hm2 i i' _ le_rfl))) (isWt_zero_pbT _ (hm2 i i' _ le_rfl))
  have wz₁ : ∀ i i', IsWt Y 0 _ (z₁ i i') := by
    intro i i'
    rw [hz₁]
    exact isWt_neg (isWt_zero_mul (isWt_zero_constFn _ _) (isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isWt_constFn_mul (isWt_inv (hinv a) (wφ b i i')) _))
  have wz₂ : ∀ i i', IsWt Y 0 _ (z₂ i i') := by
    intro i i'
    rw [hz₂]
    refine isWt_sub ?_ (isWt_zero_mul (isWt_zero_constFn _ _) (isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isWt_zero_mul (isWt_constFn_mul (wφ a i i') _) (wφ b i i')))
    exact isWt_zero_mul (hdw i 0 (V i ⊓ V i') (Y.q.left.preimage_mono inf_le_left) _
      (isWt_zero_pbT _ (hm2 i i' _ le_rfl))) (isWt_zero_pbT _ (hm2 i i' _ le_rfl))
  obtain ⟨c, y₁, hy₁w, hy₁⟩ := hH1 z₁ coc₁ wz₁
  obtain ⟨e, y₂, hy₂w, hy₂⟩ := hH1 z₂ coc₂ wz₂

  obtain ⟨d', hd'⟩ : ∃ d' : J → Fld Y.H.left, ∀ i W f, d' i W f = d i W f - ∑ a, constFn Y.H.hom W (e a) * dd a W f :=
    ⟨fun i W f => d i W f - ∑ a, constFn Y.H.hom W (e a) * dd a W f, fun _ _ _ => rfl⟩
  have hd'F : ∀ i, IsField (Y.q.left ⁻¹ᵁ V i) (d' i) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
    · simp only [hd', (hdF i).1 W hW, (hddF _).1 W le_top, mul_add, Finset.sum_add_distrib]
      ring
    · have s : ∑ a, constFn Y.H.hom W (e a) * (f * dd a W f' + f' * dd a W f) =
          f * ∑ a, constFn Y.H.hom W (e a) * dd a W f' + f' * ∑ a, constFn Y.H.hom W (e a) * dd a W f := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [hd', (hdF i).2.1 W hW, (hddF _).2.1 W le_top, s]
      ring
    · simp only [hd', (hdF i).2.2 W W' h hW f, (hddF _).2.2 W W' h le_top f, map_sub, map_sum, map_mul,
        resG_constFn]
  have hd'C : ∀ i (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i → ∀ r, d' i W (constFn Y.H.hom W r) = constFn Y.H.hom W (D r) := by
    intro i W hW r
    simp only [hd', (hlift i).2 W hW r, GlobalTheory.T.invariantVectorField_constFn_eq_zero Y.H (v _) (dd _) (hinv _) W r, mul_zero, Finset.sum_const_zero,
      sub_zero]
  have hd'K : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d' i W f - d' i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
    intro i i' W hW f
    rw [hd', hd', ← hKS i i' W hW f]
    ring

  have A1 : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' →
      rsT (y₁ i') W - rsT (y₁ i) W = -(constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) *
        ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dd a W (φ b i i' W)) - ∑ b, constFn Y.H.hom W (c b) * φ b i i' W := by
    intro i i' W hW
    have h := congrArg (fun s => rsT s W) (hy₁ i i')
    simp only [rz₁ i i' W hW, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_constFn _ hW,
      rsT_rsT inf_le_left hW, rsT_rsT inf_le_right hW] at h
    have e : ∀ b, rsT (dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) W =
        φ b i i' W := fun b => by rw [← hφ, rφ b i i' _ W le_rfl hW]
    simp only [e] at h
    linear_combination -h
  have A2 : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' →
      rsT (y₂ i') W - rsT (y₂ i) W = dlg Y.H Y.q.left Dd.toPre.P.L (d i) (j i) (j i') W -
        constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) * ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * φ a i i' W * φ b i i' W -
        ∑ b, constFn Y.H.hom W (e b) * φ b i i' W := by
    intro i i' W hW
    have h := congrArg (fun s => rsT s W) (hy₂ i i')
    simp only [rz₂ i i' W hW, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_constFn _ hW,
      rsT_rsT inf_le_left hW, rsT_rsT inf_le_right hW] at h
    have e' : ∀ b, rsT (dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) W =
        φ b i i' W := fun b => by rw [← hφ, rφ b i i' _ W le_rfl hW]
    simp only [e'] at h
    linear_combination -h
  refine ⟨Heat.mk Θ hΘ (fun a => -c a) J (fun i => Y.q.left ⁻¹ᵁ V i) j d' y₂ y₁ ?_ hUL (fun i => ⟨hd'F i, hd'C i⟩) ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hV]; rfl
  · intro k i i' W hW f
    have hg := pbT_unit' Y.q.left (Dd.toPre.P.L.g (j i) (j i')) (hm2 i i' W hW)
    have hdi : IsDer (d' i W) := isDer_of_isField (hd'F i) (hW.trans inf_le_left)
    have key := ringOp_conj hdi (fun a => hdd a W) (Θ := Θ.map (constFn Y.H.hom W)) (fun a b => hs W a b)
      (fun a => constFn Y.H.hom W (-c a)) (rsT (y₂ i) W) (rsT (y₁ i) W) hg k f
    refine key.trans ?_
    congr 1
    have F1 := hd'K i i' W hW f
    have F2 := A2 i i' W hW
    have F3 := A1 i i' W hW
    simp only [hφ] at F2 F3
    have E : d' i W (pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i')).val W) * pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W =
        dlg Y.H Y.q.left Dd.toPre.P.L (d i) (j i) (j i') W - ∑ b, constFn Y.H.hom W (e b) *
          dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W := by
      rw [hd', sub_mul, Finset.sum_mul]
      unfold dlg
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    have U1 : ∑ a, constFn Y.H.hom W (-c a) * (dd a W (pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i')).val W) *
        pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W) =
        -∑ b, constFn Y.H.hom W (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [constFn_neg]; unfold dlg; ring
    unfold dlg at F1 F2 F3 E U1
    simp only [ringOp, op, Matrix.map_apply]
    rw [E, U1]
    set g := pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i')).val W
    set gi := pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W
    linear_combination (2 * (k : Γ(Y.H.left, W))) * F1 +
      (k : Γ(Y.H.left, W)) ^ 2 * f * (-2 * F2 +
        (∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * (dd a W g * gi) * (dd b W g * gi)) * hc2 W) +
      (k : Γ(Y.H.left, W)) * f * (-2 * F3 + (∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dd a W (dd b W g * gi)) * hc2 W)
  · intro i
    refine ⟨⟨V i, rfl⟩, hy₂w i, hy₁w i, fun α V' hV' f hf => ?_⟩
    show IsWt Y α _ (d' i _ f)
    rw [hd']
    exact isWt_sub (hdw i α V' hV' f hf) (isWt_sum _ _ fun a _ => isWt_constFn_mul (isWt_inv (hinv a) hf) _)

end GlobalTheory.HeatGlue
