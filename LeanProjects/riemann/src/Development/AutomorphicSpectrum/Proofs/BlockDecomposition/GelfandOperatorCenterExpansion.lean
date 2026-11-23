import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrETransposeEqPhiSeq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegationStatement

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GenTr

section Alg

variable {A B : Type} [Ring A] [Ring B]

theorem map_bco (φ : A →+* B) (N : A) (τ : ℕ → A) (m j : ℕ) :
    φ (bco N τ m j) = bco (φ N) (φ ∘ τ) m j := by
  induction m generalizing j with
  | zero => cases j <;> simp [bco]
  | succ m ih => cases j <;> simp [bco, ih]

theorem phiSeq_unfold (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j : Fin m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq]

theorem map_phiSeq (φ : A →+* B) (N : A) (τ : ℕ → A) (m : ℕ) :
    φ (phiSeq N τ m) = phiSeq (φ N) (φ ∘ τ) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [phiSeq_unfold N, phiSeq_unfold (φ N)]
    simp only [map_sub, map_sum, map_mul, map_bco, Function.comp]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [ih j j.isLt]

theorem exists_words (P : FreeAlgebra ℂ ℕ) : ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ),
    P = ∑ i, c i • ((w i).map (FreeAlgebra.ι ℂ)).prod := by
  have hspan : P ∈ Submodule.span ℂ
      (Set.range fun w : List ℕ => (w.map (FreeAlgebra.ι ℂ)).prod) := by
    have h1 : P ∈ Algebra.adjoin ℂ (Set.range (FreeAlgebra.ι ℂ)) := by
      rw [FreeAlgebra.adjoin_range_ι]; trivial
    rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h1
    refine Submodule.span_mono ?_ h1
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact ⟨[k], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a ++ b, by simp⟩
  obtain ⟨d, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hspan
  let e := d.support.equivFin
  refine ⟨d.support.card, fun i => d (e.symm i), fun i => (e.symm i).1, ?_⟩
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  exact (Equiv.sum_comp e.symm (fun i : d.support => d i • (i.1.map (FreeAlgebra.ι ℂ)).prod)).symm

theorem phiSeq_words (n m : ℕ) : ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ),
    ∀ {A : Type} [Ring A] [Algebra ℂ A] (τ : ℕ → A),
      phiSeq (n : A) τ m = ∑ i, c i • ((w i).map τ).prod := by
  obtain ⟨N, c, w, h⟩ := exists_words (phiSeq (n : FreeAlgebra ℂ ℕ) (FreeAlgebra.ι ℂ) m)
  refine ⟨N, c, w, fun {A} _ _ τ => ?_⟩
  have h1 := map_phiSeq ((FreeAlgebra.lift ℂ τ : FreeAlgebra ℂ ℕ →ₐ[ℂ] A) : FreeAlgebra ℂ ℕ →+* A)
    (n : FreeAlgebra ℂ ℕ) (FreeAlgebra.ι ℂ) m
  have h2 : ((FreeAlgebra.lift ℂ τ : FreeAlgebra ℂ ℕ →ₐ[ℂ] A) : FreeAlgebra ℂ ℕ →+* A) ∘ (FreeAlgebra.ι ℂ) = τ := by
    funext k; simp
  rw [h2, map_natCast] at h1
  rw [← h1, h]
  simp only [map_sum, RingHom.coe_coe, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k _ => by simp

end Alg

section Ops

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

theorem diffAt {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp)

theorem Rd_add' (X : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (f + f') g = Rd X f g + Rd X f' g := by
  have := ((diffAt hf hg).hasFDerivAt.add (diffAt hf' hg).hasFDerivAt).fderiv
  simp only [Rd]
  exact DFunLike.congr_fun this _

theorem Rd_smul' (X : Mat n) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • f) g = c • Rd X f g := by
  have := ((diffAt hf hg).hasFDerivAt.const_smul c).fderiv
  simp only [Rd]
  exact DFunLike.congr_fun this _

def Du (u : ℂ) (X : Mat n) (f : Mat n → V) : Mat n → V :=
  (1 / 2 : ℂ) • (Rd X f + u • Rd (Complex.I • X) f)

theorem Eu_eq_Du (s : Bool) (a b : Fin n) (f : Mat n → V) :
    Eu s a b f = Du (if s then -Complex.I else Complex.I) (Matrix.single a b 1) f := by
  simp [Eu, Du, Matrix.smul_single]

theorem Rd_addX (X Y : Mat n) (f : Mat n → V) (g : Mat n) : Rd (X + Y) f g = Rd X f g + Rd Y f g := by
  simp [Rd, mul_add]

theorem Rd_negX (X : Mat n) (f : Mat n → V) (g : Mat n) : Rd (-X) f g = - Rd X f g := by
  simp [Rd, mul_neg]

theorem Du_sub (u : ℂ) (X Y : Mat n) (f : Mat n → V) (g : Mat n) :
    Du u (X - Y) f g = Du u X f g - Du u Y f g := by
  simp only [Du, Pi.smul_apply, Pi.add_apply, sub_eq_add_neg, smul_add, Rd_addX, Rd_negX, smul_neg]
  module

theorem Du_zero (u : ℂ) (f : Mat n → V) (g : Mat n) : Du u (0 : Mat n) f g = 0 := by
  simp [Du, Rd]

theorem Rd_Du (X : Mat n) (u : ℂ) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X ((1 / 2 : ℂ) • (f + u • f')) g = (1 / 2 : ℂ) • (Rd X f g + u • Rd X f' g) := by
  have h4 : ContDiffOn ℝ ∞ (u • f') (GLs n) := hf'.const_smul u
  have h3 : ContDiffOn ℝ ∞ (f + u • f') (GLs n) := hf.add h4
  rw [Rd_smul' X _ h3 hg, Rd_add' X hf h4 hg, Rd_smul' X _ hf' hg]

theorem Du_bracket (hR : RCalc) {u : ℂ} (hu : u * u = -1) (X Y : Mat n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Du u X (Du u Y f) g - Du u Y (Du u X f) g = Du u (X * Y - Y * X) f g := by
  obtain ⟨h1, h2, -⟩ := (hR n).1 V f hf
  have a1 := h2 X Y g hg
  have a2 := h2 X (Complex.I • Y) g hg
  have a3 := h2 (Complex.I • X) Y g hg
  have a4 := h2 (Complex.I • X) (Complex.I • Y) g hg
  have e2 : X * (Complex.I • Y) - (Complex.I • Y) * X = Complex.I • (X * Y - Y * X) := by
    simp [smul_sub]
  have e3 : (Complex.I • X) * Y - Y * (Complex.I • X) = Complex.I • (X * Y - Y * X) := by
    simp [smul_sub]
  have e4 : (Complex.I • X) * (Complex.I • Y) - (Complex.I • Y) * (Complex.I • X) = -(X * Y - Y * X) := by
    simp [smul_smul, smul_sub]
    abel
  rw [e2] at a2
  rw [e3] at a3
  rw [e4, Rd_negX] at a4
  simp only [Du, Pi.smul_apply, Pi.add_apply]
  rw [Rd_Du X u (h1 Y) (h1 _) hg, Rd_Du (Complex.I • X) u (h1 Y) (h1 _) hg,
    Rd_Du Y u (h1 X) (h1 _) hg, Rd_Du (Complex.I • Y) u (h1 X) (h1 _) hg]
  generalize Rd (X * Y - Y * X) f g = K at *
  generalize Rd (Complex.I • (X * Y - Y * X)) f g = L at *
  rw [sub_eq_iff_eq_add] at a1 a2 a3 a4
  rw [a1, a2, a3, a4]
  match_scalars <;> first | ring1 | linear_combination (-1 / 4 : ℂ) * hu | linear_combination (1 / 4 : ℂ) * hu

end Ops

section Ops2

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Sm (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] : Submodule ℂ (Mat n → V) where
  carrier := {f | ContDiffOn ℝ ∞ f (GLs n) ∧ ∀ x, x ∉ GLs n → f x = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨h1.add h3, fun x hx => by simp [h2 x hx, h4 x hx]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨h1.const_smul c, fun x hx => by simp [h2 x hx]⟩

theorem indicator_mem {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    (GLs n).indicator f ∈ Sm n V :=
  ⟨hf.congr fun x hx => by simp [hx], fun x hx => by simp [hx]⟩

theorem Eu_smooth (hR : RCalc) (s : Bool) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  obtain ⟨h1, -⟩ := (hR n).1 V f hf
  exact ((h1 _).add ((h1 _).const_smul _)).const_smul _

theorem Eu_add' (s : Bool) (a b : Fin n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu s a b (f + f') g = Eu s a b f g + Eu s a b f' g := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_add' _ hf hf' hg]
  module

theorem Eu_smul' (s : Bool) (a b : Fin n) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Eu s a b (c • f) g = c • Eu s a b f g := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_smul' _ _ hf hg]
  module

def eS (hR : RCalc) (s : Bool) (a b : Fin n) : Module.End ℂ (Sm n V) where
  toFun f := ⟨(GLs n).indicator (Eu s a b f.1), indicator_mem (Eu_smooth hR s a b f.2.1)⟩
  map_add' f f' := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · simpa [hg] using Eu_add' s a b f.2.1 f'.2.1 hg
    · simp [hg]
  map_smul' c f := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · simpa [hg] using Eu_smul' s a b c f.2.1 hg
    · simp [hg]

theorem eS_apply (hR : RCalc) (s : Bool) (a b : Fin n) (f : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (eS hR s a b f).1 g = Eu s a b f.1 g := by
  simp [eS, hg]

theorem eS_apply_off (hR : RCalc) (s : Bool) (a b : Fin n) (f : Sm n V) {g : Mat n} (hg : g ∉ GLs n) :
    (eS hR s a b f).1 g = 0 := by
  simp [eS, hg]

theorem eS_eS (hR : RCalc) (s : Bool) (a b c d : Fin n) (f : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (eS hR s a b (eS hR s c d f)).1 g = Eu s a b (Eu s c d f.1) g := by
  rw [eS_apply hR s a b _ hg]
  exact Eu_agree_GLs s a b (fun x hx => eS_apply hR s c d f hx) g hg

theorem eS_rel (hR : RCalc) (s : Bool) (a b c d : Fin n) :
    (eS hR s a b : Module.End ℂ (Sm n V)) * eS hR s c d - eS hR s c d * eS hR s a b =
      (if b = c then eS hR s a d else 0) - (if a = d then eS hR s c b else 0) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  obtain ⟨u, hu, hE⟩ : ∃ u : ℂ, u * u = -1 ∧
      ∀ (p q : Fin n) (F : Mat n → V), Eu s p q F = Du u (Matrix.single p q 1) F :=
    ⟨if s then -Complex.I else Complex.I, by cases s <;> simp, fun p q F => Eu_eq_Du s p q F⟩
  by_cases hg : g ∈ GLs n
  · have h0 : ((eS hR s a b * eS hR s c d - eS hR s c d * eS hR s a b :
        Module.End ℂ (Sm n V)) f).1 g = Eu s a b (Eu s c d f.1) g - Eu s c d (Eu s a b f.1) g := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply]
      exact congrArg₂ (· - ·) (eS_eS hR s a b c d f hg) (eS_eS hR s c d a b f hg)
    rw [h0]
    simp only [hE]
    rw [Du_bracket hR hu _ _ f.2.1 hg]
    have hm : (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 : Mat n)
        = (if b = c then Matrix.single a d 1 else 0) - (if a = d then Matrix.single c b 1 else 0) := by
      congr 1
      · split_ifs with h
        · subst h; simp
        · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
      · split_ifs with h
        · subst h; simp
        · exact Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h) _
    rw [hm, Du_sub]
    simp only [LinearMap.sub_apply]
    congr 1
    · split_ifs
      · rw [eS_apply hR s a d f hg, hE]
      · simp [Du_zero]
    · split_ifs
      · rw [eS_apply hR s c b f hg, hE]
      · simp [Du_zero]
  · have h0 : ((eS hR s a b * eS hR s c d - eS hR s c d * eS hR s a b :
        Module.End ℂ (Sm n V)) f).1 g = 0 := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply]
      change (eS hR s a b (eS hR s c d f)).1 g - (eS hR s c d (eS hR s a b f)).1 g = 0
      rw [eS_apply_off hR s a b _ hg, eS_apply_off hR s c d _ hg, sub_zero]
    rw [h0]
    have h3 : ∀ (p q : Fin n), (eS hR s p q f).1 g = 0 := fun p q => eS_apply_off hR s p q f hg
    simp only [LinearMap.sub_apply]
    change 0 = ((if b = c then eS hR s a d else 0 : Module.End ℂ (Sm n V)) f).1 g - ((if a = d then eS hR s c b else 0 : Module.End ℂ (Sm n V)) f).1 g
    split_ifs <;> simp [h3]

end Ops2

section Main

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem EpowT_agree_GLs (s : Bool) (m : ℕ) (a b : Fin n) {F F' : Mat n → V}
    (h : ∀ g ∈ GLs n, F g = F' g) : ∀ x ∈ GLs n, EpowT s m a b F x = EpowT s m a b F' x := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    by_cases hab : a = b
    · simpa [EpowT, hab] using h x hx
    · simp [EpowT, hab]
  | succ m ih =>
    intro x hx
    simp only [EpowT, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_agree_GLs s c a (ih c b) x hx

theorem gelT_agree_GLs (s : Bool) (m : ℕ) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, gelT s m F x = gelT s m F' x := by
  intro x hx
  simp only [gelT, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => EpowT_agree_GLs s m a a h x hx

theorem Epw_apply (hR : RCalc) (s : Bool) (f : Sm n V) (m : ℕ) (a b : Fin n) :
    ∀ g ∈ GLs n, (Epw (eS (V := V) hR s) m a b f).1 g = Epow s m a b f.1 g := by
  induction m generalizing a b with
  | zero =>
    intro g hg
    by_cases hab : a = b
    · subst hab; simp [Epw, Epow]
    · simp [Epw, Epow, hab]
  | succ m ih =>
    intro g hg
    simp only [Epw, Epow, Finset.sum_apply, LinearMap.sum_apply, Module.End.mul_apply,
      AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eS_apply hR s a c _ hg]
    exact Eu_agree_GLs s a c (ih c b) g hg

theorem EpwT_apply (hR : RCalc) (s : Bool) (f : Sm n V) (m : ℕ) (a b : Fin n) :
    ∀ g ∈ GLs n, (Epw (fun a b => eS (V := V) hR s b a) m a b f).1 g = EpowT s m a b f.1 g := by
  induction m generalizing a b with
  | zero =>
    intro g hg
    by_cases hab : a = b
    · subst hab; simp [Epw, EpowT]
    · simp [Epw, EpowT, hab]
  | succ m ih =>
    intro g hg
    simp only [Epw, EpowT, Finset.sum_apply, LinearMap.sum_apply, Module.End.mul_apply,
      AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eS_apply hR s c a _ hg]
    exact Eu_agree_GLs s c a (ih c b) g hg

theorem trE_apply (hR : RCalc) (s : Bool) (f : Sm n V) (j : ℕ) :
    ∀ g ∈ GLs n, (trE (eS (V := V) hR s) j f).1 g = gel s j f.1 g := by
  intro g hg
  simp only [trE, gel, Finset.sum_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finset_sum]
  exact Finset.sum_congr rfl fun a _ => Epw_apply hR s f j a a g hg

theorem trET_apply (hR : RCalc) (s : Bool) (f : Sm n V) (j : ℕ) :
    ∀ g ∈ GLs n, (trE (fun a b => eS (V := V) hR s b a) j f).1 g = gelT s j f.1 g := by
  intro g hg
  simp only [trE, gelT, Finset.sum_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finset_sum]
  exact Finset.sum_congr rfl fun a _ => EpwT_apply hR s f j a a g hg

theorem prod_apply (hR : RCalc) (s : Bool) (f : Sm n V) (w : List ℕ) :
    ∀ g ∈ GLs n, (((w.map (trE (eS (V := V) hR s))).prod : Module.End ℂ (Sm n V)) f).1 g =
      zOp (w.map fun j => (s, j)) f.1 g := by
  induction w with
  | nil => intro g hg; simp [zOp]
  | cons p w ih =>
    intro g hg
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [trE_apply hR s _ p g hg]
    exact gel_agree_GLs s p ih g hg

end Main

theorem transposed_invariants : ∀ (n m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ), (∀ cc : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = ∑ i, c i * ((w i).map (GlobalTheory.Dec.gelfVal cc)).prod) ∧ (RCalc → ∀ (s : Bool) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, gelT s m f x = ∑ i, c i • zOp ((w i).map (fun j => (s, j))) f x) := by
  intro n m
  obtain ⟨N, c, w, h⟩ := phiSeq_words n m
  refine ⟨N, c, w, fun cc => ?_, fun hR s V _ _ f hf x hx => ?_⟩
  · rw [GlobalTheory.T.gelfand_value_negation, h (A := ℂ)]
    simp
  · let F : Sm n V := ⟨(GLs n).indicator f, indicator_mem hf⟩
    have hF : ∀ g ∈ GLs n, f g = F.1 g := fun g hg => by simp [F, hg]
    have key := GlTranspose.trE_transpose_eq_phiSeq n (eS (n := n) (V := V) hR s) (eS_rel hR s) m
    rw [h (trE (eS (n := n) (V := V) hR s))] at key
    rw [gelT_agree_GLs s m hF x hx, ← trET_apply hR s F m x hx, key]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, AddSubmonoidClass.coe_finset_sum,
      Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prod_apply hR s F (w i) x hx, zOp_agree_GLs n _ f F.1 hF x hx]

end GlobalTheory.CompanionTheory.WaveMult.GenTr
