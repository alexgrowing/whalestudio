import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignSwap
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}

def evalHom (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* T :=
  (w.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom

theorem valT_eq (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) : valT w U f = evalHom w U h f :=
  dif_pos h

theorem valT_res (w : Sp T ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ V) (f : Γ(X, U)) :
    valT w V (rs X hle f) = valT w U f := by
  have h' : ⊤ ≤ w ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq w U h']
  change ((X.presheaf.map (homOfLE hle).op ≫ w.appLE V ⊤ h) ≫ _).hom f = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem valT_comp (φ : T →+* T') (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) :
    valT (spMap φ ≫ w) U f = φ (valT w U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ w) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valT_eq _ U h', valT_eq w U h]
  have e : (spMap φ ≫ w).appLE U ⊤ h' = w.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  unfold evalHom
  rw [e, Category.assoc]
  erw [Scheme.ΓSpecIso_naturality]
  rfl

theorem valT_cst (w : Sp T ⟶ X) (π : X ⟶ Sp T) (hw : w ≫ π = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (a : T) :
    valT w U (cst π U a) = a := by
  have e := valT_res w (le_top : U ≤ ⊤) h (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a))
  refine e.trans ?_
  rw [valT_eq w ⊤ (fun _ _ => trivial)]
  have e2 : w.appLE ⊤ ⊤ (fun _ _ => trivial) = w.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  unfold evalHom
  rw [e2]
  change ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ (π.appTop ≫ w.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom a = a
  rw [← Scheme.Hom.comp_appTop, hw]
  simp

def trU (w : Sp T ⟶ X) (L : LB X) (c c' : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ L.U c') : Tˣ :=
  Units.map (evalHom w (L.U c ⊓ L.U c') (fun _ hp => ⟨h hp, h' hp⟩)).toMonoidHom (L.g c c')

theorem trU_val (w : Sp T ⟶ X) (L : LB X) (c c' : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ L.U c') :
    (trU w L c c' h h').val = valT w (L.U c ⊓ L.U c') (L.g c c').val := (valT_eq _ _ _ _).symm

theorem valT_sec (w : Sp T ⟶ X) (L : LB X) (c c' : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ L.U c') (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) :
    valT w (L.U c) (s.f c) = (trU w L c c' h h').val ^ l * valT w (L.U c') (s.f c') := by
  have hh : ⊤ ≤ w ⁻¹ᵁ (L.U c ⊓ L.U c') := fun _ hp => ⟨h hp, h' hp⟩
  have e : rs X (inf_le_left : L.U c ⊓ L.U c' ≤ L.U c) (s.f c) =
      ((L.g c c') ^ (l : ℤ)).val * rs X (inf_le_right : L.U c ⊓ L.U c' ≤ L.U c') (s.f c') := s.compat c c'
  have e1 := valT_res w (inf_le_left : L.U c ⊓ L.U c' ≤ L.U c) hh (s.f c)
  have e2 := valT_res w (inf_le_right : L.U c ⊓ L.U c' ≤ L.U c') hh (s.f c')
  rw [← e1, ← e2, e, trU_val, valT_eq _ _ hh, valT_eq _ _ hh, valT_eq _ _ hh, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]

theorem section_ext {K : Type} [Field K] (π : X ⟶ Sp K) (w w' : Sp K ⟶ X) (hw : w ≫ π = 𝟙 _) (hw' : w' ≫ π = 𝟙 _)
    (p p' : Sp K) (e : w p = w' p') : w = w' := by
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  obtain rfl := hs p p'
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (w p)) isOpen_univ
  have h : ⊤ ≤ w ⁻¹ᵁ U := fun q _ => by rw [hs q p]; exact hxU
  have h' : ⊤ ≤ w' ⁻¹ᵁ U := fun q _ => by rw [hs q p]; change w' p ∈ U; rw [← e]; exact hxU
  have key : ∀ (v : Sp K ⟶ X) (hv : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), IsUnit (evalHom v U hv f) ↔ v p ∈ X.basicOpen f := by
    intro v hv f
    have e1 : IsUnit (evalHom v U hv f) ↔ IsUnit ((v.appLE U ⊤ hv).hom f) :=
      isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
    rw [e1]
    have e2 := Scheme.basicOpen_appLE v ⊤ U hv f
    constructor
    · intro hu
      have : p ∈ (Sp K).basicOpen ((v.appLE U ⊤ hv).hom f) := by
        rw [Scheme.basicOpen_of_isUnit _ hu]; trivial
      erw [e2] at this
      exact this.2
    · intro hp
      apply RingedSpace.isUnit_of_isUnit_germ
      intro q hq
      have : q ∈ (Sp K).basicOpen ((v.appLE U ⊤ hv).hom f) := by
        erw [e2]; rw [hs q p]; exact ⟨trivial, hp⟩
      exact ((Sp K).mem_basicOpen _ q hq).1 this
  have hev : evalHom w U h = evalHom w' U h' := by
    ext f
    have h1 : evalHom w U h (f - cst π U (evalHom w U h f)) = 0 := by
      rw [map_sub, ← valT_eq w U h (cst _ _ _), valT_cst w π hw U h, sub_self]
    have h2 : ¬ IsUnit (evalHom w' U h' (f - cst π U (evalHom w U h f))) := by
      rw [key, ← e, ← key w h, h1]; exact not_isUnit_zero
    rw [isUnit_iff_ne_zero, not_not, map_sub, ← valT_eq w' U h' (cst _ _ _), valT_cst w' π hw' U h', sub_eq_zero] at h2
    exact h2.symm
  have happ : w.appLE U ⊤ h = w'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom]
    exact CommRingCat.hom_ext hev
  have a1 := IsAffineOpen.SpecMap_appLE_fromSpec w hU (isAffineOpen_top (Sp K)) h
  have a2 := IsAffineOpen.SpecMap_appLE_fromSpec w' hU (isAffineOpen_top (Sp K)) h'
  rw [happ, a2, IsAffineOpen.fromSpec_top] at a1
  exact ((cancel_epi _).1 a1).symm

variable {R : Type} [CommRing R]

theorem fst_translate (x : KeyIn R) (z : Pt x) (k : Fin x.P.g) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * x.v k).left = z.left := by
  let io : 𝟙_ (Over (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have h1 : io ≫ x.v k = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over (Sp R)))) (𝟙 _), Category.id_comp]
    exact Over.OverMorphism.ext (x.basis.1 k)
  have h2 : io ≫ ((toUnit (epsR R) ≫ z) * x.v k) = z := by
    rw [MonObj.comp_mul, h1, _root_.mul_one, ← Category.assoc, toUnit_unique (io ≫ toUnit _) (𝟙 _), Category.id_comp]
  exact congrArg (·.left) h2

theorem top_le_translate (x : KeyIn R) (z : Pt x) (k : Fin x.P.g) {U : x.P.A.left.Opens} (h : ⊤ ≤ z.left ⁻¹ᵁ U) :
    ⊤ ≤ (show Sp (DualNumber R) ⟶ x.P.A.left from ((toUnit (epsR R) ≫ z) * x.v k).left) ⁻¹ᵁ U := by
  intro p _
  have hp : (p : PrimeSpectrum (DualNumber R)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro a ha
    have ha' : a.fst = 0 := ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 = 0 := by ext <;> simp [ha', pow_two]
    rw [this]; exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  have := h (Set.mem_univ q)
  rw [← fst_translate x z k] at this
  exact this

theorem jac_chart (x : KeyIn R) {n : ℕ} (s : Fin x.P.g → RR x n) (z : Pt x) (c c' : x.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c')
    (h0 : ∀ i, valT (T := R) z.left (x.P.L.U c') ((s i).f c') = 0) :
    jac x s z c = (trU (T := R) z.left x.P.L c c' h h').val ^ (x.P.g * n) * jac x s z c' := by
  unfold jac
  rw [mul_comm x.P.g n, pow_mul]
  have hd : ∀ (a : R) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), a ^ x.P.g * M.det = (a • M).det := fun a M => by
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [hd]
  congr 1
  ext i k
  have hk := top_le_translate x z k h
  have hk' := top_le_translate x z k h'
  have e1 : (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left (x.P.L.U c') ((s i).f c')).fst = 0 := by
    have := valT_comp (TrivSqZeroExt.fstHom R R R).toRingHom _ _ hk' ((s i).f c')
    erw [fst_translate x z k, h0 i] at this
    exact this.symm
  have e2 : ((trU (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left x.P.L c c' hk hk').val).fst =
      (trU (T := R) z.left x.P.L c c' h h').val := by
    have := valT_comp (TrivSqZeroExt.fstHom R R R).toRingHom _ (x.P.L.U c ⊓ x.P.L.U c')
      (fun _ hp => ⟨hk hp, hk' hp⟩) (x.P.L.g c c').val
    erw [fst_translate x z k] at this
    rw [trU_val, trU_val]
    exact this.symm
  rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply]
  erw [valT_sec _ x.P.L c c' hk hk' n (s i)]
  rw [TrivSqZeroExt.snd_mul]
  erw [e1]
  rw [TrivSqZeroExt.fst_pow, e2]
  simp

end GlobalTheory.KaUnique
end
noncomputable section
namespace GlobalTheory.KaUnique

section Comb
variable {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) (L : LB X)

def IsComb {N : ℕ} (b : Fin N → ∀ i, Γ(X, L.U i)) (c : Fin N → R) (f : ∀ i, Γ(X, L.U i)) : Prop :=
  ∀ i, f i = ∑ k, cst π (L.U i) (c k) * b k i

variable {π L}

theorem IsComb.mulVec {N N' : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {b' : Fin N' → ∀ i, Γ(X, L.U i)}
    {M : Matrix (Fin N) (Fin N') R} {u f : ∀ i, Γ(X, L.U i)} {e : Fin N' → R}
    (hM : ∀ k, IsComb π L b (fun k' => M k' k) (fun i => u i * b' k i)) (he : IsComb π L b' e f) :
    IsComb π L b (M.mulVec e) (fun i => u i * f i) := by
  intro i
  simp only [he i, Finset.mul_sum, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hM k i
  simp only at this
  rw [mul_left_comm, this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k' _ => by ring

theorem IsComb.mulVec' {N N' : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {b' : Fin N' → ∀ i, Γ(X, L.U i)}
    {M : Matrix (Fin N) (Fin N') R} {f : ∀ i, Γ(X, L.U i)} {e : Fin N' → R}
    (hM : ∀ k, IsComb π L b (fun k' => M k' k) (b' k)) (he : IsComb π L b' e f) :
    IsComb π L b (M.mulVec e) f := by
  have := IsComb.mulVec (u := fun _ => 1) (M := M) (b := b) (b' := b') (by simpa only [_root_.one_mul] using hM) he
  simpa only [_root_.one_mul] using this

theorem IsComb.single {N : ℕ} (b : Fin N → ∀ i, Γ(X, L.U i)) (k : Fin N) :
    IsComb π L b (fun k' => (1 : Matrix (Fin N) (Fin N) R) k' k) (b k) := by
  intro i
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ h; simp [Matrix.one_apply_ne h]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem IsComb.valT {N : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {c : Fin N → R} {f : ∀ i, Γ(X, L.U i)}
    (h : IsComb π L b c f) (w : Sp R ⟶ X) (hw : w ≫ π = 𝟙 _) (i : L.ι) (hi : ⊤ ≤ w ⁻¹ᵁ L.U i) :
    valT w (L.U i) (f i) = ∑ k, valT w (L.U i) (b k i) * c k := by
  rw [h i, valT_eq w _ hi, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← valT_eq, ← valT_eq, valT_cst w π hw _ hi, mul_comm]

def combSec {M : LB X} {N : ℕ} (b : Fin N → LB.Sec M) (c : Fin N → R) : LB.Sec M where
  f := fun i => ∑ k, cst π (M.U i) (c k) * (b k).f i
  compat := fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, (b k).compat i j, rs_cst, rs_cst]
    ring

end Comb

variable {R : Type} [CommRing R]

abbrev fam (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) : Fin N → ∀ i, Γ(x.P.A.left, x.P.L.U i) := fun k => (b k).f

theorem comb_unique {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) {c c' : Fin N → R}
    {f : ∀ i, Γ(x.P.A.left, x.P.L.U i)} (h : IsComb x.P.A.hom x.P.L (fam x b) c f)
    (h' : IsComb x.P.A.hom x.P.L (fam x b) c' f) : c = c' := by
  have e : (combSec (π := x.P.A.hom) b c).f = f := funext fun i => (h i).symm
  exact (hb (combSec (π := x.P.A.hom) b c)).unique (fun i => (congrFun e i).trans (h i))
    (fun i => (congrFun e i).trans (h' i))

theorem exists_change {x : KeyIn R} {l N : ℕ} {b b' : Fin N → RR x l} (hb : IsBasis x b) (hb' : IsBasis x b') :
    ∃ B : (Matrix (Fin N) (Fin N) R)ˣ, ∀ k, IsComb x.P.A.hom x.P.L (fam x b) (fun k' => B.val k' k) (fam x b' k) := by
  choose c hc using fun k => (hb (b' k)).exists
  choose c' hc' using fun k => (hb' (b k)).exists
  have h1 : ∀ k, IsComb x.P.A.hom x.P.L (fam x b) (fun k' => (Matrix.of fun a k => c k a) k' k) (fam x b' k) := hc
  have h2 : ∀ k, IsComb x.P.A.hom x.P.L (fam x b') (fun k' => (Matrix.of fun a k => c' k a) k' k) (fam x b k) := hc'
  refine ⟨⟨Matrix.of fun a k => c k a, Matrix.of fun a k => c' k a, ?_, ?_⟩, h1⟩
  · ext a k
    exact congrFun (comb_unique hb (IsComb.mulVec' h1 (h2 k)) (IsComb.single _ k)) a
  · ext a k
    exact congrFun (comb_unique hb' (IsComb.mulVec' h2 (h1 k)) (IsComb.single _ k)) a

theorem isMul_comb {x : KeyIn R} {n l : ℕ} {s : Fin x.P.g → RR x n}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m) (i j) (hj : j < x.P.g) (k) :
    IsComb x.P.A.hom x.P.L (fam x (b j)) (fun k' => m i j (j + 1) k' k) (fun c => fam x s i c * fam x (b (j + 1)) k c) :=
  hm i j hj k

theorem isCx_of_isMul {x : KeyIn R} {n l d : ℕ} {s : Fin x.P.g → RR x n} {z : Fin d → Pt x} {ch : Fin d → x.P.L.ι}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j)) (hz : EtZ x s z ch) :
    IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m
      (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) := by
  refine isCx_kosD (N := fun j => (l - j * n) ^ x.P.g) m _ (fun i i' j hj => ?_) (fun i => ?_)
  · ext a k
    have h1 := IsComb.mulVec (isMul_comb hm i j (by omega)) (isMul_comb hm i' (j + 1) hj k)
    have h2 := IsComb.mulVec (isMul_comb hm i' j (by omega)) (isMul_comb hm i (j + 1) hj k)
    simp only [mul_left_comm (fam x s i' _) (fam x s i _)] at h2
    exact congrFun (comb_unique (hb j (by omega)) h1 h2) a
  · ext a k
    have h1 := (isMul_comb hm i 0 x.g_pos k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
    refine h1.symm.trans ?_
    have h2 : valT (T := R) (z a).left (x.P.L.U (ch a)) (fam x s i (ch a)) = 0 := hz.2.1 a i
    rw [valT_eq _ _ (hz.1 a)] at h2
    beta_reduce
    rw [valT_eq _ _ (hz.1 a), map_mul, h2, zero_mul]
    rfl

end GlobalTheory.KaUnique
end
