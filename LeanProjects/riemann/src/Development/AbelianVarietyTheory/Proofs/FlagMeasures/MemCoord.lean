import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

def hq {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := ∑ i, ∑ j, x i * Hm i j * sig (y j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_add_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (a + b) y = _root_.GlobalTheory.HL.SAN.hq sig Hm a y + _root_.GlobalTheory.HL.SAN.hq sig Hm b y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_smul_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (c • a) y = c * _root_.GlobalTheory.HL.SAN.hq sig Hm a y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def eQ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun v := v + hq sig Hm v u • x - hq sig Hm v x • (u + s • x)
  map_add' a b := by
    simp only [hq_add_l]; module
  map_smul' c a := by
    simp only [hq_smul_l, RingHom.id_apply]; module

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.mem_coord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} (x : Fin N → E) :
    x ∈ Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin N → E)) ↔ ∀ j, x j ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · subst h; simp [L.O.one_mem]
      · simp [Pi.single_apply, h, L.O.zero_mem]
    | zero => intro j; exact L.O.zero_mem
    | add y z _ _ hy hz => intro j; exact add_mem (hy j) (hz j)
    | smul c y _ hy =>
      intro j
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hy j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : L.O) • (Pi.single j 1 : Fin N → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem hf_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x y : Fin N → E} (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    hf L Hm x y ∈ L.O :=
  L.O.sum_mem fun i _ => L.O.sum_mem fun j _ =>
    L.O.mul_mem (L.O.mul_mem (hx i) (hI i j)) (GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem hf_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) (x y : Fin n → E) (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    _root_.GlobalTheory.HL.hf L H x y ∈ L.O := by
  unfold _root_.GlobalTheory.HL.hf
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hx i) (hI i j)) (_root_.GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem eich_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) {x u : Fin n → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) {v : Fin n → E} (hv : ∀ j, v j ∈ L.O) (j : Fin n) :
    _root_.GlobalTheory.HL.eich L H x u s v j ∈ L.O := by
  unfold _root_.GlobalTheory.HL.eich
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sub_mem (add_mem (hv j) (mul_mem (hf_mem_O L hI v u hv hu) (hx j)))
    (mul_mem (hf_mem_O L hI v x hv hx) (add_mem (hu j) (mul_mem hs (hx j))))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.int_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by
  intro m
  induction m with
  | zero =>
    intro X u s e _ _ _ _ x hx j
    simpa using hx j
  | succ m ih =>
    intro X u s e hX hu hs he x hx j
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, he 0]
    exact eich_mem_O L hI (hX 0) (hu 0) (hs 0)
      (fun j' => ih (fun i => X i.succ) (fun i => u i.succ) (fun i => s i.succ) (fun i => e i.succ)
        (fun i => hX i.succ) (fun i => hu i.succ) (fun i => hs i.succ) (fun i => he i.succ) x hx j') j

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.ext_prod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ} : ∀ (m : ℕ)
    (a : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (b : Fin m → (Fin N → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin N → (A.loc p).Ep)),
    (∀ i, A.Ext p (a i) (b i)) →
      A.Ext p (List.ofFn a).prod (List.ofFn b).prod := by
  intro m
  induction m with
  | zero =>
    intro a b _
    simp only [_root_.GlobalTheory.HL.Places.Ext]
    intro x
    simp
  | succ m ih =>
    intro a b h
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
    simp only [_root_.GlobalTheory.HL.Places.Ext] at h ih' ⊢
    intro x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, ih', h 0]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.bc_eQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by
  have h5 := (_root_.GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm
  have hu := h5 v u
  have hx := h5 v x
  unfold _root_.GlobalTheory.HL.eich
  rw [hu, hx]
  funext i
  simp [_root_.GlobalTheory.HL.Places.bc, _root_.GlobalTheory.HL.SAN.eQ, _root_.GlobalTheory.HL.SAN.hq]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField F)).ne'⟩⟩

end GlobalTheory.HL.SAN
