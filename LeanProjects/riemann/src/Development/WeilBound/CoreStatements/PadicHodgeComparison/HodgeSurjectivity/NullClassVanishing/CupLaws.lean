import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.TfBaseField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopyStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace CrystallineSemistableComparison.Onto.RCupLaws

open GlobalTheory.EtC

section Gen

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{w} R}

def om {a N p : ℕ} (α : SimplexCategory.mk a ⟶ SimplexCategory.mk N) (e : a = p) : Fin (p + 1) → Fin (N + 1) :=
  fun i => α.toOrderHom (Fin.cast (by subst e; rfl) i)

theorem om_mono {a N p : ℕ} (α : SimplexCategory.mk a ⟶ SimplexCategory.mk N) (e : a = p) : Monotone (om α e) :=
  fun i j hij => α.toOrderHom.monotone ((Fin.cast_le_cast _).2 hij)

theorem term_zero (F : C ⥤ ModuleCat.{w} R) {p n : ℕ} (s : ComposableArrows C n) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : CH.term F s (0 : CH.Cn F p) g hg = 0 :=
  map_zero _

variable (P : CH.Pairing F₁ F₂ F₃) {p q : ℕ} (f : CH.Cn F₁ p) (g : CH.Cn F₂ q)

def val {N : ℕ} (s : ComposableArrows C N) (z : Pr N) : F₃.obj (s.obj (Fin.last N)) :=
  if h : z.1 = p ∧ z.2.1 = q then
    P.μ _ (CH.term F₁ s f (om z.2.2.1 h.1) (om_mono _ _)) (CH.term F₂ s g (om z.2.2.2 h.2) (om_mono _ _))
  else 0

def phi {N : ℕ} (s : ComposableArrows C N) : (Pr N →₀ ℤ) →ₗ[ℤ] F₃.obj (s.obj (Fin.last N)) :=
  Finsupp.linearCombination ℤ (val P f g s)

theorem phi_single {N : ℕ} (s : ComposableArrows C N) (z : Pr N) (t : ℤ) :
    phi P f g s (Finsupp.single z t) = t • val P f g s z :=
  Finsupp.linearCombination_single _ _ _

theorem val_pos {N : ℕ} (s : ComposableArrows C N) (z : Pr N) (h : z.1 = p ∧ z.2.1 = q) :
    val P f g s z =
      P.μ _ (CH.term F₁ s f (om z.2.2.1 h.1) (om_mono _ _)) (CH.term F₂ s g (om z.2.2.2 h.2) (om_mono _ _)) :=
  dif_pos h

theorem val_neg {N : ℕ} (s : ComposableArrows C N) (z : Pr N) (h : ¬ (z.1 = p ∧ z.2.1 = q)) : val P f g s z = 0 :=
  dif_neg h

theorem val_mk {N : ℕ} (s : ComposableArrows C N) (α : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk N) :
    val P f g s ⟨p, q, α, β⟩ = P.μ _ (CH.term F₁ s f (fun i : Fin (p + 1) => α.toOrderHom i) α.toOrderHom.monotone)
      (CH.term F₂ s g (fun i : Fin (q + 1) => β.toOrderHom i) β.toOrderHom.monotone) :=
  val_pos P f g s _ ⟨rfl, rfl⟩

theorem d₁_zero {N r : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (β : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, α, β⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N a r : ℕ} (α : SimplexCategory.mk (a + 1) ⟶ SimplexCategory.mk N)
    (β : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨a + 1, r, α, β⟩ : Pr N) =
      ∑ i : Fin (a + 2), Finsupp.single (⟨a, r, SimplexCategory.δ i ≫ α, β⟩ : Pr N) ((-1) ^ (i : ℕ)) := rfl

theorem d₂_zero {N a : ℕ} (α : SimplexCategory.mk a ⟶ SimplexCategory.mk N) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨a, 0, α, β⟩ : Pr N) = 0 := rfl

theorem d₂_succ {N a r : ℕ} (α : SimplexCategory.mk a ⟶ SimplexCategory.mk N)
    (β : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨a, r + 1, α, β⟩ : Pr N) =
      ∑ j : Fin (r + 2), Finsupp.single (⟨a, r, α, SimplexCategory.δ j ≫ β⟩ : Pr N) ((-1) ^ (j : ℕ)) := rfl

theorem phi_d₁ (hf : CH.d F₁ p f = 0) {N : ℕ} (s : ComposableArrows C N) (z : Pr N) : phi P f g s z.d₁ = 0 := by
  obtain ⟨a, r, α, β⟩ := z
  cases a with
  | zero => rw [d₁_zero, map_zero]
  | succ a =>
    rw [d₁_succ, map_sum]
    simp only [phi_single]
    by_cases h : a = p ∧ r = q
    · obtain ⟨rfl, rfl⟩ := h
      have e := CrystallineSemistableComparison.Auxff.term_d F₁ s f (fun i : Fin (a + 2) => α.toOrderHom i) α.toOrderHom.monotone
      rw [hf, term_zero] at e
      have e2 := congrArg ((P.μ _).flip (CH.term F₂ s g (fun i : Fin (r + 1) => β.toOrderHom i) β.toOrderHom.monotone)) e
      simp only [map_zero, map_sum, map_zsmul, LinearMap.flip_apply] at e2
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e2.symm
      rw [val_mk]
      rfl
    · exact Finset.sum_eq_zero fun i _ => by rw [val_neg P f g s _ h, smul_zero]

theorem phi_d₂ (hg : CH.d F₂ q g = 0) {N : ℕ} (s : ComposableArrows C N) (z : Pr N) : phi P f g s z.d₂ = 0 := by
  obtain ⟨a, r, α, β⟩ := z
  cases r with
  | zero => rw [d₂_zero, map_zero]
  | succ r =>
    rw [d₂_succ, map_sum]
    simp only [phi_single]
    by_cases h : a = p ∧ r = q
    · obtain ⟨rfl, rfl⟩ := h
      have e := CrystallineSemistableComparison.Auxff.term_d F₂ s g (fun i : Fin (r + 2) => β.toOrderHom i) β.toOrderHom.monotone
      rw [hg, term_zero] at e
      have e2 := congrArg (P.μ _ (CH.term F₁ s f (fun i : Fin (a + 1) => α.toOrderHom i) α.toOrderHom.monotone)) e
      simp only [map_zero, map_sum, map_zsmul] at e2
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e2.symm
      rw [val_mk]
      rfl
    · exact Finset.sum_eq_zero fun i _ => by rw [val_neg P f g s _ h, smul_zero]

theorem phi_d (hf : CH.d F₁ p f = 0) (hg : CH.d F₂ q g = 0) {N : ℕ} (s : ComposableArrows C N) (c : Pr N →₀ ℤ) :
    phi P f g s (Pr.d N c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add c c' hc hc' => rw [map_add, map_add, hc, hc', add_zero]
  | single z t =>
    rw [Pr.d, Finsupp.linearCombination_single, map_smul, map_add, map_smul, phi_d₁ P f g hf, phi_d₂ P f g hg,
      smul_zero, add_zero, smul_zero]

theorem phi_face {N : ℕ} (s : ComposableArrows C (N + 1)) (i : Fin (N + 2)) (c : Pr N →₀ ℤ) :
    (F₃.map (GlobalTheory.CatH.toLast i s)).hom (phi P f g (GlobalTheory.CatH.face i s) c) = phi P f g s (Pr.push (SimplexCategory.δ i) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c c' hc hc' => simp only [map_add, hc, hc']
  | single z t =>
    obtain ⟨a, r, α, β⟩ := z
    rw [phi_single, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, phi_single, map_zsmul]
    congr 1
    by_cases h : a = p ∧ r = q
    · obtain ⟨rfl, rfl⟩ := h
      rw [val_mk, val_mk, ← P.nat, CH.term_face, CH.term_face]
      rfl
    · rw [val_neg P f g _ _ h, val_neg P f g _ _ h, map_zero]

def hc {N : ℕ} (c : Pr N →₀ ℤ) : CH.Cn F₃ N := fun s => phi P f g s c

theorem d_hc {N : ℕ} (c : Pr N →₀ ℤ) (s : ComposableArrows C (N + 1)) :
    CH.d F₃ N (hc P f g c) s = phi P f g s (Pr.bd c) := by
  change ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • (F₃.map (GlobalTheory.CatH.toLast i s)).hom (phi P f g (GlobalTheory.CatH.face i s) c) = _
  rw [Pr.bd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← phi_face]

theorem phi_aw {n : ℕ} (h : p + q = n) (s : ComposableArrows C n) : phi P f g s (Pr.aw n) = P.cupC h f g s := by
  rw [Pr.aw, map_sum, Finset.sum_eq_single (⟨p, by omega⟩ : Fin (n + 1))]
  · rw [phi_single, one_smul, val_pos P f g s _ ⟨rfl, show n - p = q by omega⟩, CrystallineSemistableComparison.Auxff.cupC_apply]
    exact congrArg₂ (fun x y => P.μ _ x y)
      (CH.term_congr F₁ s f _ _ (funext fun i => Fin.ext rfl))
      (CH.term_congr F₂ s g _ _ (funext fun i => Fin.ext (show (i : ℕ) + p = p + i from Nat.add_comm _ _)))
  · intro b _ hb
    rw [phi_single, val_neg, smul_zero]
    rintro ⟨h1, -⟩
    exact hb (Fin.ext h1)
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem phi_wa {n : ℕ} (h' : q + p = n) (s : ComposableArrows C n) :
    phi P f g s (Pr.wa n) = (-1 : ℤ) ^ (p * q) •
      P.μ _ (CH.term F₁ s f (CH.back h') (CH.back_mono h')) (CH.term F₂ s g (CH.front h') (CH.front_mono h')) := by
  rw [Pr.wa, map_sum, Finset.sum_eq_single (⟨q, by omega⟩ : Fin (n + 1))]
  · rw [phi_single, val_pos P f g s _ ⟨show n - q = p by omega, rfl⟩]
    have e2 : ((-1 : ℤ) ^ (q * (n - q))) = (-1) ^ (p * q) := by rw [show n - q = p by omega, mul_comm]
    refine Eq.trans (congrArg (fun t : ℤ => t • P.μ _ (CH.term F₁ s f _ (om_mono _ _)) (CH.term F₂ s g _ (om_mono _ _))) e2) ?_
    exact congrArg _ (congrArg₂ (fun x y => P.μ _ x y)
      (CH.term_congr F₁ s f _ _ (funext fun i => Fin.ext (show (i : ℕ) + q = q + i from Nat.add_comm _ _)))
      (CH.term_congr F₂ s g _ _ (funext fun i => Fin.ext rfl)))
  · intro b _ hb
    rw [phi_single, val_neg, smul_zero]
    rintro ⟨-, h2⟩
    exact hb (Fin.ext h2)
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem key (P' : CH.Pairing F₂ F₁ F₃) (hP : ∀ T x y, P'.μ T y x = P.μ T x y) (hf : CH.d F₁ p f = 0)
    (hg : CH.d F₂ q g = 0) {n : ℕ} (h : p + q = n) (h' : q + p = n) :
    P.cupC h f g - (-1 : ℤ) ^ (p * q) • P'.cupC h' g f ∈ (CH.cx F₃).B n := by
  obtain ⟨hh, -, hd0, hds⟩ := GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy
  have ev : ∀ s : ComposableArrows C n,
      (P.cupC h f g - (-1 : ℤ) ^ (p * q) • P'.cupC h' g f) s = phi P f g s (Pr.aw n - Pr.wa n) := by
    intro s
    rw [map_sub, phi_aw P f g h, phi_wa P f g h', ← hP, ← CrystallineSemistableComparison.Auxff.cupC_apply P' h' g f s]
    rfl
  cases n with
  | zero =>
    have e0 : P.cupC h f g - (-1 : ℤ) ^ (p * q) • P'.cupC h' g f = 0 := funext fun s => by
      rw [ev, ← hd0, phi_d P f g hf hg]
      rfl
    rw [e0]
    exact zero_mem _
  | succ N =>
    refine ⟨hc P f g (hh N), funext fun s => ?_⟩
    rw [ev, ← hds N, map_add, phi_d P f g hf hg, zero_add]
    exact d_hc P f g (hh N) s

end Gen

theorem cls_zsmul {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} (k : ℤ) (a : K.X n) (ha : K.d n a = 0)
    (hb : K.d n (k • a) = 0) : K.cls (k • a) hb = k • K.cls a ha := by
  have e : (⟨k • a, hb⟩ : K.Z n) = k • (⟨a, ha⟩ : K.Z n) := Subtype.ext (by simp)
  show Submodule.Quotient.mk _ = _
  rw [e]
  exact map_zsmul (Submodule.mkQ _) k _

theorem cup_comm {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{w} R}
    (P : CH.Pairing F₁ F₂ F₃) (P' : CH.Pairing F₂ F₁ F₃) (hP : ∀ T x y, P'.μ T y x = P.μ T x y) {p q n : ℕ}
    (h : p + q = n) (h' : q + p = n) (x : CH.H F₁ p) (y : CH.H F₂ q) :
    P.cup h x y = (-1 : ℤ) ^ (p * q) • P'.cup h' y x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F₁) p).1 x
  obtain ⟨g, hg, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F₂) q).1 y
  obtain ⟨c1, e1⟩ := CrystallineSemistableComparison.P.cup_cls P h f g hf hg
  obtain ⟨c2, e2⟩ := CrystallineSemistableComparison.P.cup_cls P' h' g f hg hf
  rw [e1, e2]
  have hc3 : CH.d F₃ n ((-1 : ℤ) ^ (p * q) • P'.cupC h' g f) = 0 := by rw [map_zsmul, c2, smul_zero]
  refine Eq.trans ?_ (cls_zsmul (K := CH.cx F₃) _ _ c2 hc3)
  exact ((CrystallineSemistableComparison.P.cls_surj (CH.cx F₃) n).2.2.1 _ _ c1 hc3).2 (key P f g P' hP hf hg h h')

theorem hdg_comm {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (ha' : a' + a = c) (h : i + j = n) (h' : j + i = n) (x : HT.Hdg q a i) (y : HT.Hdg q a' j) :
    HT.cupH q ha h x y = (-1 : ℤ) ^ (i * j) • HT.cupH q ha' h' y x :=
  cup_comm (HT.grOk (CrystallineSemistableComparison.smFun X q) ha).pair (HT.grOk (CrystallineSemistableComparison.smFun X q) ha').pair (fun T x y => by
      obtain ⟨x, hx, rfl⟩ := HT.sq_surj _ _ x
      obtain ⟨y, hy, rfl⟩ := HT.sq_surj _ _ y
      rw [HT.pair_mk, HT.pair_mk]
      exact HT.mk_congr _ _ (mul_comm _ _) _ _) h h' x y

end CrystallineSemistableComparison.Onto.RCupLaws

open CrystallineSemistableComparison.Onto.RCupLaws in
theorem CrystallineSemistableComparison.Onto.cupLaws_pf : CrystallineSemistableComparison.Onto.CupLaws := by
  intro K _ X q
  have F := CrystallineSemistableComparison.HT.kForm
  refine ⟨fun ha h => F.bilin q ha h, fun h₁ h₂ h₃ h₄ g₁ g₂ g₃ g₄ x y z => F.assoc q h₁ h₂ h₃ h₄ g₁ g₂ g₃ g₄ x y z,
    fun ha ha' h h' x y => hdg_comm q ha ha' h h' x y, fun x => (F.one_cup q _ _ x).1,
    fun Y p u hu _ _ _ _ _ _ ha h x y => F.pull_cup u hu ha h x y, fun a n x => F.pull_id q (𝟙 X) _ rfl a n x,
    fun Y Y' p p' u hu v hv w hw e a n x => ?_⟩
  subst e
  exact (F.pull_comp v hv u hu hw a n x).symm
