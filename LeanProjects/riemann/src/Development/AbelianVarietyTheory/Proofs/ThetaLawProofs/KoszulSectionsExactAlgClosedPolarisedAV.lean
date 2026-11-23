import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemSpanOfForallGermMemSpan
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsMaximalOfFinitePrimes
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfRegular
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CubeCutRegularSequence
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RingKrullDimLocalizationQuotientLe
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLeNatCastNeZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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
open GlobalTheory

noncomputable section
namespace GlobalTheory.KosField

theorem mem_iSup_range_iff {R M N J : Type} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Fintype J] (P : J → Prop) [DecidablePred P] (φ : J → M →ₗ[R] N) (y : N) :
    y ∈ (⨆ (j : J) (_ : P j), LinearMap.range (φ j)) ↔
      ∃ t : J → M, y = ∑ j ∈ Finset.univ.filter P, φ j (t j) := by
  classical
  constructor
  · intro hy
    refine Submodule.iSup_induction (motive := fun y => ∃ t : J → M, y = ∑ j ∈ Finset.univ.filter P, φ j (t j))
      _ hy (fun j z hz => ?_) ⟨0, by simp⟩ ?_
    · by_cases hj : P j
      · rw [iSup_pos hj] at hz
        obtain ⟨w, rfl⟩ := hz
        refine ⟨Pi.single j w, ?_⟩
        rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero])
          (fun h => absurd (by simpa using hj) h), Pi.single_eq_same]
      · rw [iSup_neg hj, Submodule.mem_bot] at hz
        exact ⟨0, by simp [hz]⟩
    · rintro a b ⟨t, rfl⟩ ⟨u, rfl⟩
      exact ⟨t + u, by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨t, rfl⟩
    refine Submodule.sum_mem _ fun j hj => ?_
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (by simpa using hj) ⟨t j, rfl⟩)

theorem regular_step {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (h : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) (i : Fin g) (a : R) (r : Fin g → R)
    (e : f i * a = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), f j * r j) :
    ∃ r' : Fin g → R, a = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), f j * r' j := by
  have hi : (i : ℕ) < (List.ofFn f).length := by simp
  have h1 := h.regular_mod_prev i hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 : Ideal.ofList ((List.ofFn f).take i) =
      ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range (LinearMap.mulLeft R (f j)) := by
    apply le_antisymm
    · rw [Ideal.ofList, Ideal.span_le]
      intro z hz
      obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hz
      have hk' : k < g := by simp at hk; omega
      refine Submodule.mem_iSup_of_mem (⟨k, hk'⟩ : Fin g) (Submodule.mem_iSup_of_mem (by simp at hk ⊢; omega) ⟨1, ?_⟩)
      simp
    · refine iSup₂_le fun j hj => ?_
      rintro _ ⟨z, rfl⟩
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
      exact List.mem_take_iff_getElem.2 ⟨j, by simp; omega, by simp⟩
  rw [h2] at h1
  exact (mem_iSup_range_iff _ _ _).1 (h1 a ((mem_iSup_range_iff _ _ _).2 ⟨r, by simpa using e⟩))

variable {X : Scheme.{0}} {L : LB X} {n l l' : ℤ} {V W : X.Opens}

def sf (s : LB.Sec (pw L n)) (k : L.ι) : Γ(X, L.U k) := s.f k

def co (x : SecOn (pw L l) V) (k : L.ι) : Γ(X, V ⊓ L.U k) := GlobalTheory.LB.coord x k

theorem co_ext {x y : SecOn (pw L l) V} (h : ∀ k, co x k = co y k) : x = y := GlobalTheory.LB.sec_ext h

theorem co_add (x y : SecOn (pw L l) V) (k : L.ι) : co (x + y) k = co x k + co y k := rfl
theorem co_sub (x y : SecOn (pw L l) V) (k : L.ι) : co (x - y) k = co x k - co y k := rfl
theorem co_zero (k : L.ι) : co (0 : SecOn (pw L l) V) k = 0 := rfl
theorem co_smul (a : Γ(X, V)) (x : SecOn (pw L l) V) (k : L.ι) :
    co (a • x) k = rs X inf_le_left a * co x k := rfl
theorem co_restrict (h : W ≤ V) (x : SecOn (pw L l) V) (k : L.ι) :
    co (SecOn.restrict _ h x) k = rs X (inf_le_inf_right _ h) (co x k) := rfl
theorem co_ofSec (s : LB.Sec (pw L l)) (k : L.ι) :
    co (GlobalTheory.LB.ofSec s V) k = rs X inf_le_right (sf s k) := rfl
theorem co_sum {J : Type} (T : Finset J) (x : J → SecOn (pw L l) V) (k : L.ι) :
    co (∑ j ∈ T, x j) k = ∑ j ∈ T, co (x j) k := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, ih]

theorem co_compat (x : SecOn (pw L l) V) (i j : L.ι) {O : X.Opens} (hi : O ≤ V ⊓ L.U i) (hj : O ≤ V ⊓ L.U j)
    (hij : O ≤ L.U i ⊓ L.U j) :
    rs X hi (co x i) = rs X hij (L.g i j ^ l).val * rs X hj (co x j) :=
  SecOn.compat x i j hi hj hij

theorem sf_compat (s : LB.Sec (pw L n)) (i j : L.ι) {O : X.Opens} (hi : O ≤ L.U i) (hj : O ≤ L.U j)
    (hij : O ≤ L.U i ⊓ L.U j) :
    rs X hi (sf s i) = rs X hij (L.g i j ^ n).val * rs X hj (sf s j) :=
  GlobalTheory.LB.sec_rel s i j hi hj hij

def pwMk (l : ℤ) (y : ∀ k : L.ι, Γ(X, V ⊓ L.U k))
    (hy : ∀ (i j : L.ι) (O : X.Opens) (hi : O ≤ V ⊓ L.U i) (hj : O ≤ V ⊓ L.U j) (hij : O ≤ L.U i ⊓ L.U j),
      rs X hi (y i) = rs X hij (L.g i j ^ l).val * rs X hj (y j)) : SecOn (pw L l) V :=
  GlobalTheory.LB.mkSec (L := pw L l) y fun i j => hy i j _ _ _ _

theorem co_pwMk (y : ∀ k : L.ι, Γ(X, V ⊓ L.U k)) (hy) (k : L.ι) : co (pwMk l y hy) k = y k := rfl

def mulEq (s : LB.Sec (pw L n)) (h : l' = l + n) (V : X.Opens) :
    SecOn (pw L l) V →ₗ[Γ(X, V)] SecOn (pw L l') V where
  toFun x := pwMk l' (fun k => rs X inf_le_right (sf s k) * co x k) fun i j O hi hj hij => by
    rw [map_mul, map_mul, rs_rs, rs_rs, co_compat x i j hi hj hij,
      sf_compat s i j _ (hij.trans inf_le_right) hij, h, zpow_add, Units.val_mul, map_mul]
    ring
  map_add' x y := co_ext fun k => by simp only [co_pwMk, co_add, mul_add]
  map_smul' a x := co_ext fun k => mul_left_comm _ _ _

def mulPw (s : LB.Sec (pw L n)) (l l' : ℤ) (V : X.Opens) :
    SecOn (pw L l) V →ₗ[Γ(X, V)] SecOn (pw L l') V :=
  if h : l' = l + n then mulEq s h V else 0

theorem co_mulPw (s : LB.Sec (pw L n)) (h : l' = l + n) (x : SecOn (pw L l) V) (k : L.ι) :
    co (mulPw s l l' V x) k = rs X inf_le_right (sf s k) * co x k := by
  rw [mulPw, dif_pos h]; rfl

theorem mulPw_restrict (s : LB.Sec (pw L n)) (h : W ≤ V) (x : SecOn (pw L l) V) :
    mulPw s l l' W (SecOn.restrict _ h x) = SecOn.restrict _ h (mulPw s l l' V x) := by
  by_cases e : l' = l + n
  · exact co_ext fun k => by simp only [co_mulPw s e, co_restrict, map_mul, rs_rs]
  · simp only [mulPw, dif_neg e, LinearMap.zero_apply, map_zero]

theorem mulPw_comm (s s' : LB.Sec (pw L n)) {l'' : ℤ} (h : l' = l + n) (h' : l'' = l' + n)
    (x : SecOn (pw L l) V) :
    mulPw s' l' l'' V (mulPw s l l' V x) = mulPw s l' l'' V (mulPw s' l l' V x) :=
  co_ext fun k => by
    rw [co_mulPw _ h', co_mulPw _ h', co_mulPw _ h, co_mulPw _ h, mul_left_comm]

def ch (hL : L.IsLB) (l : ℤ) (k : L.ι) (h : V ≤ L.U k) : SecOn (pw L l) V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  SecOn.chart (isLB_pw hL l) k h

theorem ch_apply (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) (x : SecOn (pw L l) V) :
    ch hL l k h x = rs X (le_inf le_rfl h) (co x k) := rfl

theorem ch_mulPw (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) (s : LB.Sec (pw L n)) (e : l' = l + n)
    (x : SecOn (pw L l) V) : ch hL l' k h (mulPw s l l' V x) = rs X h (sf s k) * ch hL l k h x := by
  rw [ch_apply, ch_apply, co_mulPw s e, map_mul, rs_rs]

theorem sum_mulPw_iff (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) {J : Type} (T : Finset J)
    (s : J → LB.Sec (pw L n)) (e : l' = l + n) (y : SecOn (pw L l') V) :
    (∃ t : J → SecOn (pw L l) V, y = ∑ j ∈ T, mulPw (s j) l l' V (t j)) ↔
      ∃ r : J → Γ(X, V), ch hL l' k h y = ∑ j ∈ T, rs X h (sf (s j) k) * r j := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fun j => ch hL l k h (t j), by simp only [map_sum, ch_mulPw hL k h _ e]⟩
  · rintro ⟨r, hr⟩
    refine ⟨fun j => (ch hL l k h).symm (r j), (ch hL l' k h).injective ?_⟩
    simp only [hr, map_sum, ch_mulPw hL k h _ e, LinearEquiv.apply_symm_apply]

variable {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {κ : Type} (D : κ → X.Opens)

def mulCube (s : LB.Sec (pw L n)) (l l' : ℤ) : secCube f (pw L l) D ⟶ secCube f (pw L l') D :=
  secCubeMap f D (mulPw s l l') (mulPw_restrict s)

theorem mulCube_comm (s s' : LB.Sec (pw L n)) (l l' l'' : ℤ) (h : l' = l + n) (h' : l'' = l' + n) :
    mulCube f D s l l' ≫ mulCube f D s' l' l'' = mulCube f D s' l l' ≫ mulCube f D s l' l'' := by
  ext T x
  exact mulPw_comm s s' h h' x

theorem mem_mulCube_iff {J : Type} [Fintype J] (P : J → Prop) [DecidablePred P] (s : J → LB.Sec (pw L n))
    (T : Finset κ) (y : SecOn (pw L l') (⨅ i ∈ T, D i)) :
    (show (secCube f (pw L l') D).obj T from y) ∈
      (⨆ (j : J) (_ : P j), LinearMap.range ((mulCube f D (s j) l l').app T).hom) ↔
      ∃ t : J → SecOn (pw L l) (⨅ i ∈ T, D i),
        y = ∑ j ∈ Finset.univ.filter P, mulPw (s j) l l' _ (t j) :=
  mem_iSup_range_iff P _ _

theorem exists_sec_sum_of_ofSec_eq_sum (hV : V = ⊤) {J : Type} (T : Finset J) (s : J → LB.Sec (pw L n)) (e : l' = l + n)
    (y : LB.Sec (pw L l')) (h : ∃ t : J → SecOn (pw L l) V,
      (GlobalTheory.LB.ofSec y V : SecOn (pw L l') V) = ∑ j ∈ T, mulPw (s j) l l' V (t j)) :
    ∃ ta : J → LB.Sec (pw L l), ∀ k, sf y k = ∑ j ∈ T, sf (s j) k * sf (ta j) k := by
  obtain ⟨t, ht⟩ := h
  choose ta hta using fun j => (SecOn.ofSec_bijective (M := pw L l) hV).2 (t j)
  refine ⟨ta, fun k => ?_⟩
  have hk : L.U k ≤ V ⊓ L.U k := le_inf (hV ▸ le_top) le_rfl
  have := congrArg (fun z => rs X hk (co z k)) ht
  simp only [co_sum, co_mulPw _ e, ← hta, co_ofSec, map_sum, map_mul, rs_rs, rs_self] at this
  exact this

theorem gs_rs (y : X) (h : W ≤ V) (hy : y ∈ W) (a : Γ(X, V)) :
    gs (𝟙 X) y W (rs X h a) = gs (𝟙 X) y V a := gs_res (𝟙 X) y h hy a

theorem gs_germ (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = (X.presheaf.germ V y hy).hom a := gs_eq (𝟙 X) y V hy a

theorem gs_sub' (y : X) (hy : y ∈ V) (a b : Γ(X, V)) :
    gs (𝟙 X) y V (a - b) = gs (𝟙 X) y V a - gs (𝟙 X) y V b := by
  simp only [gs_germ y hy, map_sub]

theorem gs_co_change (x : SecOn (pw L l) V) (y : X) (hy : y ∈ V) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gs (𝟙 X) y (V ⊓ L.U k) (co x k) =
      gs (𝟙 X) y (L.U k ⊓ L.U k') (L.g k k' ^ l).val * gs (𝟙 X) y (V ⊓ L.U k') (co x k') := by
  have hO : y ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hy, hk⟩, hk'⟩
  have := congrArg (gs (𝟙 X) y _) (co_compat x k k' (O := V ⊓ L.U k ⊓ L.U k') inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right))
  rwa [gs_mul _ y _ hO, gs_rs y _ hO, gs_rs y _ hO, gs_rs y _ hO] at this

theorem gs_sf_change (s : LB.Sec (pw L n)) (y : X) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gs (𝟙 X) y (L.U k) (sf s k) =
      gs (𝟙 X) y (L.U k ⊓ L.U k') (L.g k k' ^ n).val * gs (𝟙 X) y (L.U k') (sf s k') := by
  have hO : y ∈ L.U k ⊓ L.U k' := ⟨hk, hk'⟩
  have := congrArg (gs (𝟙 X) y _) (sf_compat s k k' inf_le_left inf_le_right le_rfl)
  rwa [gs_mul _ y _ hO, gs_rs y _ hO, gs_rs y _ hO, gs_rs y _ hO] at this

def zI {J : Type} (s : J → LB.Sec (pw L n)) (y : X) (k : L.ι) : Ideal (X.presheaf.stalk y) :=
  Ideal.span (Set.range fun i => gs (𝟙 X) y (L.U k) (sf (s i) k))

theorem zI_le {J : Type} (s : J → LB.Sec (pw L n)) (y : X) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    zI s y k ≤ zI s y k' := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  simp only [gs_sf_change (s i) y hk hk']
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem zI_eq {J : Type} (s : J → LB.Sec (pw L n)) (y : X) {k : L.ι} (h : V ≤ L.U k) (hy : y ∈ V) :
    Ideal.span (Set.range fun i => gs (𝟙 X) y V (rs X h (sf (s i) k))) = zI s y k := by
  simp only [gs_rs y h hy, zI]

theorem mem_basicOpen_iff (s : LB.Sec (pw L n)) (y : X) {k : L.ι} (h : V ≤ L.U k) (hy : y ∈ V) :
    y ∈ X.basicOpen (rs X h (sf s k)) ↔ y ∈ Out.nonzeroLocus s := by
  rw [X.mem_basicOpen _ y hy, ← gs_germ y hy, gs_rs y h hy]
  constructor
  · intro hu
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [gs_germ y (h hy)] at hu
    exact (X.mem_basicOpen (sf s k) y (h hy)).2 hu
  · intro hn
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 hn
    have hy' : y ∈ L.U k' := X.basicOpen_le (sf s k') hk'
    have hu := (X.mem_basicOpen (sf s k') y hy').1 hk'
    rw [← gs_germ y hy', gs_sf_change s y hy' (h hy)] at hu
    exact isUnit_of_mul_isUnit_right hu

theorem gs_ch (hL : L.IsLB) {k : L.ι} (h : V ≤ L.U k) (x : SecOn (pw L l) V) (y : X) (hy : y ∈ V) :
    gs (𝟙 X) y V (ch hL l k h x) = gs (𝟙 X) y (V ⊓ L.U k) (co x k) := gs_rs y _ hy _

theorem gs_sum_mem {J : Type} (T : Finset J) (s : J → LB.Sec (pw L n)) (e : l' = l + n)
    (t : J → SecOn (pw L l) V) (y : X) (hy : y ∈ V) {k : L.ι} (hk : y ∈ L.U k) :
    gs (𝟙 X) y (V ⊓ L.U k) (co (∑ j ∈ T, mulPw (s j) l l' V (t j)) k) ∈ zI s y k := by
  have hO : y ∈ V ⊓ L.U k := ⟨hy, hk⟩
  rw [co_sum, gs_germ y hO, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [co_mulPw _ e, map_mul, ← gs_germ y hO, gs_rs y _ hO]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem sum_of_germs (hL : L.IsLB) (hV : IsAffineOpen V) {k : L.ι} (h : V ≤ L.U k) {g : ℕ}
    (s : Fin g → LB.Sec (pw L n)) (e : l' = l + n) (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y))
    (σ : SecOn (pw L l') V)
    (hσ : ∀ y : X, y ∈ V → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      gs (𝟙 X) y (V ⊓ L.U (c y)) (co σ (c y)) ∈ zI s y (c y)) :
    ∃ t : Fin g → SecOn (pw L l) V,
      σ = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < g), mulPw (s j) l l' V (t j) := by
  rw [sum_mulPw_iff hL k h _ s e, Finset.filter_true_of_mem (fun j _ => j.2)]
  have := GlobalTheory.mem_span_of_forall_germ_mem_span X V (Fin g) (fun i => rs X h (sf (s i) k)) (ch hL l' k h σ) hV fun y hy hz => by
    rw [zI_eq s y h hy, gs_ch hL h σ y hy, gs_co_change σ y hy (h hy) (hc y)]
    exact Ideal.mul_mem_left _ _ (zI_le s y (hc y) (h hy)
      (hσ y hy fun i hi => hz i ((mem_basicOpen_iff (s i) y h hy).2 hi)))
  obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.1 this
  exact ⟨r, by rw [← hr]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _⟩

theorem exists_interp {K : Type} [Field K] (p : X ⟶ Sp K) (hp : LocallyOfFiniteType p)
    (hL : L.IsLB) (hV : IsAffineOpen V) {k : L.ι} (h : V ≤ L.U k) {J : Type}
    (s : J → LB.Sec (pw L n)) (hZ : Set.Finite {y : X | ∀ i, y ∉ Out.nonzeroLocus (s i)})
    (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y)) (a : ∀ y : X, X.presheaf.stalk y) (l : ℤ) :
    ∃ σ : SecOn (pw L l) V, ∀ y : X, y ∈ V → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      gs (𝟙 X) y (V ⊓ L.U (c y)) (co σ (c y)) - a y ∈ zI s y (c y) := by
  obtain ⟨r, hr⟩ := GlobalTheory.GermInterp.exists_germ_sub_mem K X p V J (fun i => rs X h (sf (s i) k))
    (fun y => gs (𝟙 X) y (L.U (c y) ⊓ L.U k) ((L.g (c y) k ^ l)⁻¹).val * a y) hp hV
    (hZ.subset fun y hy i hi => hy.2 i ((mem_basicOpen_iff (s i) y h hy.1).2 hi))
  refine ⟨(ch hL l k h).symm r, fun y hy hz => ?_⟩
  have h1 := hr y hy fun i hi => hz i ((mem_basicOpen_iff (s i) y h hy).1 hi)
  have hO : y ∈ L.U (c y) ⊓ L.U k := ⟨hc y, h hy⟩
  rw [zI_eq s y h hy] at h1
  have h2 := Ideal.mul_mem_left _ (gs (𝟙 X) y (L.U (c y) ⊓ L.U k) (L.g (c y) k ^ l).val)
    (zI_le s y (h hy) (hc y) h1)
  rw [mul_sub, ← _root_.mul_assoc, ← gs_mul _ y _ hO, Units.mul_inv, gs_germ y hO 1, map_one, _root_.one_mul] at h2
  rwa [gs_co_change _ y hy (hc y) (h hy), ← gs_ch hL h _ y hy, LinearEquiv.apply_symm_apply]

theorem biInf_empty : (⨅ i ∈ (∅ : Finset κ), D i) = ⊤ := by simp

theorem mem_biInf_of_forall (T : Finset κ) (y : X) (h : ∀ a ∈ T, y ∈ D a) : y ∈ ⨅ i ∈ T, D i := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [biInf_empty]; trivial
  | insert a s _ ih =>
    rw [Finset.iInf_insert]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

theorem regular_cube (hL : L.IsLB) {g : ℕ} (s : Fin g → LB.Sec (pw L n)) (T : Finset κ) (k : L.ι)
    (h : ⨅ i ∈ T, D i ≤ L.U k)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, ⨅ i ∈ T, D i) (List.ofFn fun i => rs X h (sf (s i) k)))
    (i : Fin g) (l l' : ℤ) (y : (secCube f (pw L l) D).obj T) (e : l' = l + n)
    (hy : ((mulCube f D (s i) l l').app T).hom y ∈
      (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mulCube f D (s j) l l').app T).hom)) :
    y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mulCube f D (s j) (l - n) l).app T).hom := by
  obtain ⟨r, hr⟩ := (sum_mulPw_iff hL k h _ s e _).1
    ((mem_mulCube_iff f D (fun j : Fin g => (j : ℕ) < i) s T (mulPw (s i) l l' _ y)).1 hy)
  replace hr := (ch_mulPw hL k h (s i) e y).symm.trans hr
  exact (mem_mulCube_iff f D (fun j : Fin g => (j : ℕ) < i) s T y).2
    ((sum_mulPw_iff hL k h _ s (sub_add_cancel l n).symm y).2 (regular_step _ hreg i _ r hr))

theorem cut_global {K : Type} [Field K] (p : X ⟶ Sp K) [IsSeparated p] (hp : LocallyOfFiniteType p)
    [CompactSpace X] (hL : L.IsLB) {g : ℕ} (s : Fin g → LB.Sec (pw L n)) (hn : 0 < n)
    (hZ : Set.Finite {y : X | ∀ i, y ∉ Out.nonzeroLocus (s i)})
    (hreg : ∀ (V : X.Opens) (k : L.ι) (h : V ≤ L.U k), IsAffineOpen V →
      RingTheory.Sequence.IsWeaklyRegular Γ(X, V) (List.ofFn fun i => rs X h (sf (s i) k)))
    (hvan : ∀ (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → X.Opens), 1 ≤ l →
      (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ q, (cubeComplex (secCube p (pw L l) D)).ExactAt q)
    (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y)) :
    (∀ (i : Fin g) (l : ℤ) (y : LB.Sec (pw L l)) (ta : Fin g → LB.Sec (pw L l)), (i : ℕ) * n < l →
      (∀ k, sf (s i) k * sf y k =
        ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), sf (s j) k * sf (ta j) k) →
      ∀ d : ℤ, d = l - n → ∃ tb : Fin g → LB.Sec (pw L d), ∀ k, sf y k =
        ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), sf (s j) k * sf (tb j) k) ∧
    ∀ l : ℤ, g * n < l →
      (∀ a : ∀ y : X, X.presheaf.stalk y, ∃ sg : LB.Sec (pw L l), ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) →
        gs (𝟙 X) y (L.U (c y)) (sf sg (c y)) - a y ∈ zI s y (c y)) ∧
      ∀ sg : LB.Sec (pw L l), (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) →
        gs (𝟙 X) y (L.U (c y)) (sf sg (c y)) ∈ zI s y (c y)) →
        ∀ d : ℤ, d = l - n → ∃ ta : Fin g → LB.Sec (pw L d), ∀ k, sf sg k = ∑ j, sf (s j) k * sf (ta j) k := by
  classical
  obtain ⟨I, _, D, kk, hD, hle, hcov⟩ := exists_finite_affine_refinement hL
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  haveI : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from p]
    infer_instance
  have haff : ∀ T : Finset I, T.Nonempty → IsAffineOpen (⨅ i ∈ T, D i) := fun T hT =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hT) fun i _ => hD i
  have hin : ∀ (T : Finset I) a, a ∈ T → ⨅ i ∈ T, D i ≤ L.U (kk a) := fun T a ha =>
    (biInf_le _ ha).trans (hle a)
  have htop : ⨆ i, D i = ⊤ := top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hcov y)
  obtain ⟨H1, H2⟩ := GlobalTheory.cube_cut_regular_sequence K I g n (fun l => secCube p (pw L l) D)
    (fun i => mulCube p D (s i)) hn (fun i j => mulCube_comm p D (s i) (s j))
    (fun T hT i l l' y e hy => by
      obtain ⟨a, ha⟩ := hT
      exact regular_cube p D hL s T (kk a) (hin T a ha) (hreg _ _ _ (haff T ⟨a, ha⟩)) i l l' y e hy)
    (fun l hl => hvan l I D hl hD htop)
  refine ⟨fun i l y ta hi e d hd => ?_, fun l hl => ⟨fun a => ?_, fun sg hsg d hd => ?_⟩⟩
  · subst hd
    refine exists_sec_sum_of_ofSec_eq_sum (biInf_empty D) _ s (sub_add_cancel l n).symm y
      ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < i) s ∅ _).1
        (H1 i l (l + n) (GlobalTheory.LB.ofSec y _ : SecOn (pw L l) _) rfl hi
          ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < i) s ∅
            (mulPw (s i) l (l + n) _ (GlobalTheory.LB.ofSec y _))).2 ⟨fun j => GlobalTheory.LB.ofSec (ta j) _, co_ext fun k => ?_⟩)))
    simp only [co_sum, co_mulPw _ rfl, co_ofSec, ← map_mul, ← map_sum, e k]
  · choose σ hσ using fun b : I => exists_interp p hp hL (haff {b} (by simp)) (hin {b} b (by simp)) s hZ c hc a l
    obtain ⟨y₀, hy₀⟩ := (H2 l hl).2 σ fun b b' => by
      have h1 := iInf_le_iInf_of_subset D (show ({b} : Finset I) ⊆ {b, b'} by simp)
      have h2 := iInf_le_iInf_of_subset D (show ({b'} : Finset I) ⊆ {b, b'} by simp)
      refine (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b, b'}
        (SecOn.restrict _ h1 (σ b) - SecOn.restrict _ h2 (σ b'))).2
        (sum_of_germs hL (haff _ (by simp)) (hin _ b (by simp)) s (sub_add_cancel l n).symm c hc _
          fun y hy hz => ?_)
      have hO : y ∈ (⨅ i ∈ ({b, b'} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
      rw [co_sub, co_restrict, co_restrict, gs_sub' y hO, gs_rs y _ hO, gs_rs y _ hO]
      have := Ideal.sub_mem _ (hσ b y (h1 hy) hz) (hσ b' y (h2 hy) hz)
      rwa [sub_sub_sub_cancel_right] at this
    obtain ⟨sg, rfl⟩ := (SecOn.ofSec_bijective (M := pw L l) (biInf_empty D)).2 y₀
    refine ⟨sg, fun y hz => ?_⟩
    obtain ⟨b, hb⟩ := hcov y
    have hy : y ∈ ⨅ i ∈ ({b} : Finset I), D i := mem_biInf_of_forall D _ y (by simpa using hb)
    have hO : y ∈ (⨅ i ∈ ({b} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
    obtain ⟨t, ht⟩ := (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b}
      (SecOn.restrict _ (iInf_le_iInf_of_subset D (Finset.empty_subset {b})) (GlobalTheory.LB.ofSec sg _) - σ b)).1 (hy₀ b)
    have h1 := gs_sum_mem (Finset.univ.filter (fun j : Fin g => (j : ℕ) < g)) s (sub_add_cancel l n).symm t y hy (hc y)
    rw [← ht, SecOn.restrict_ofSec, co_sub, co_ofSec, gs_sub' y hO, gs_rs y _ hO] at h1
    have := Ideal.add_mem _ h1 (hσ b y hy hz)
    rwa [sub_add_sub_cancel] at this
  · subst hd
    have := exists_sec_sum_of_ofSec_eq_sum (biInf_empty D) _ s (sub_add_cancel l n).symm sg
      ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s ∅ _).1
        ((H2 l hl).1 (GlobalTheory.LB.ofSec sg _ : SecOn (pw L l) _) fun b => by
          refine (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b}
            (SecOn.restrict _ (iInf_le_iInf_of_subset D (Finset.empty_subset {b})) (GlobalTheory.LB.ofSec sg _))).2
            (sum_of_germs hL (haff _ (by simp)) (hin _ b (by simp)) s (sub_add_cancel l n).symm c hc _
              fun y hy hz => ?_)
          have hO : y ∈ (⨅ i ∈ ({b} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
          rw [SecOn.restrict_ofSec, co_ofSec, gs_rs y _ hO]
          exact hsg y hz))
    rwa [Finset.filter_true_of_mem (fun j _ => j.2)] at this

end GlobalTheory.KosField

namespace GlobalTheory

open KosField in

theorem koszul_sections_exact_field : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  intro hlaw K _ _ x n l s b m c hn hl hZ hb hm hc
  haveI := x.P.isAb.proper
  haveI : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  obtain ⟨H1, H2⟩ := cut_global (n := (n : ℤ)) x.P.A.hom inferInstance x.P.isLB s (by exact_mod_cast hn) hZ
    (fun V k h hV => GlobalTheory.KeyKa.isWeaklyRegular_of_finZ hlaw K x n s V k h hn hZ hV)
    (fun l I _ _ D => GlobalTheory.PolVanishing.exactAt_secCube_pw hlaw K x.P l I D) c hc
  have hl' : (x.P.g : ℤ) * n < l := by exact_mod_cast hl
  refine ⟨GlobalTheory.KeyKa.KosBasis.koszul_exact_of_regular K x n l s b m hl hb hm fun i j hij y ta e => ?_, (H2 l hl').1, fun sg hsg => ?_⟩
  · have h1 : (j + 1 + i) * n < l := lt_of_le_of_lt (Nat.mul_le_mul_right n hij) hl
    have h2 : (i : ℕ) * n < l - (j + 1) * n := by rw [add_mul] at h1; omega
    have H := H1 i _ y ta (by exact_mod_cast h2) e
    rcases Nat.eq_zero_or_pos i with hi | hi
    · obtain ⟨tb, htb⟩ := H _ rfl
      refine ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun k => ?_⟩
      have h0 : Finset.univ.filter (fun j : Fin x.P.g => (j : ℕ) < i) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun j _ => by omega
      have := htb k
      rw [h0, Finset.sum_empty] at this
      refine this.trans (Finset.sum_eq_zero fun j _ => ?_).symm
      exact mul_zero _
    · refine H _ ?_
      have h3 : n ≤ (i : ℕ) * n := Nat.le_mul_of_pos_left n hi
      have h4 : (j + 2) * n = (j + 1) * n + n := by ring
      omega
  · refine (H2 l hl').2 sg hsg _ ?_
    have h3 : n ≤ x.P.g * n := Nat.le_mul_of_pos_left n x.g_pos
    omega

end GlobalTheory
