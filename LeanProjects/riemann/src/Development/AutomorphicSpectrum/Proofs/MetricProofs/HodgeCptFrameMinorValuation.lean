import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

def ColFac {Ω : Type} [Field Ω] (R : Subring Ω) {a b : ℕ} (M : Matrix (Fin a) (Fin b) Ω) (X : Ω) : Prop :=
  ∃ (U : Matrix (Fin a) (Fin b) Ω) (U' : Matrix (Fin b) (Fin a) Ω),
    (∀ i j, U i j ∈ R) ∧ (∀ i j, U' i j ∈ R) ∧ U' * U = 1 ∧ M = X • U

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)

def inlB (k₀ : K₀) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inl k₀, fun r h => by
    unfold blkF at h
    split_ifs at h
    simp at h⟩

def fullW (τ : Ψ) (hp : 0 < p) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inr ⟨.inl τ, ⟨p - 1, by show p - 1 < p; omega⟩⟩, fun r h => by
    unfold blkF at h
    split_ifs at h with hr
    have e := Sum.inr_injective (Option.some_injective _ h)
    unfold stepOf at e
    split_ifs at e with hl
    · have : (r.2 : ℕ) = p - 1 := by
        rcases r with ⟨τ', i⟩
        simp only [Sigma.mk.injEq, Sum.inl.injEq] at e
        obtain ⟨rfl, e2⟩ := e
        simpa using Fin.val_eq_of_eq (eq_of_heq e2)
      exact hr.1 (by omega)
    · exact Sum.inr_ne_inl (congrArg Sigma.fst e)⟩

def fullO (τ : Ψ) (hq : 0 < q) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inr ⟨.inr τ, ⟨q - 1, by show q - 1 < q; omega⟩⟩, fun r h => by
    unfold blkF at h
    split_ifs at h with hr
    have e := Sum.inr_injective (Option.some_injective _ h)
    unfold stepOf at e
    split_ifs at e with hl
    · exact Sum.inl_ne_inr (congrArg Sigma.fst e)
    · have : (r.2 : ℕ) - p = q - 1 := by
        rcases r with ⟨τ', i⟩
        simp only [Sigma.mk.injEq, Sum.inr.injEq] at e
        obtain ⟨rfl, e2⟩ := e
        simpa using Fin.val_eq_of_eq (eq_of_heq e2)
      exact hr.2 (by have := r.2.2; omega)⟩

abbrev FrameD (n : Ψ ⊕ Ψ → ℕ) (J₀ : K₀ → Type) (Ω : Type) [Field Ω] (p q : ℕ) : Type :=
  FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀)

variable {A x₀}

def c₀ (F : FrameD n J₀ Ω p q) (k₀ : K₀) : J₀ k₀ := F.c (inlB k₀)

variable (A x₀)

def chartX (F : FrameD n J₀ Ω p q) : Ω := ∏ k₀, x₀ ⟨k₀, c₀ F k₀⟩

def zW (F : FrameD n J₀ Ω p q) (τ : Ψ) (hp : 0 < p) : Ω := xb A x₀ ⟨fullW τ hp, F.c (fullW τ hp)⟩

def zO (F : FrameD n J₀ Ω p q) (τ : Ψ) (hq : 0 < q) : Ω := xb A x₀ ⟨fullO τ hq, F.c (fullO τ hq)⟩

def wtOf (r : Ψ × Fin (p + q)) : ℕ := rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)

def FrameIds (F : FrameD n J₀ Ω p q) : Prop :=
  (∀ τ, IsBlockDiag p (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
  (∀ r k, blkF Ψ p q K₀ r = some k → ∀ (i : idx J₀ n k) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω),
    IsBlockDiag p h →
    detFac p r.2 (F.T r.1) * ∑ I, coefF A ⟨k, i⟩ I * minorIJ (F.T r.1 * h) I (stepCols (p + q) p r.2) =
      (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * ∑ I, F.u ⟨k, i⟩ I * minorIJ h I (stepCols (p + q) p r.2)) ∧
  (∀ r k, blkF Ψ p q K₀ r = some k → ∀ I I', IsStepRows (p + q) p r.2 I → IsStepRows (p + q) p r.2 I' →
    ∑ i : idx J₀ n k, F.u' I ⟨k, i⟩ * F.u ⟨k, i⟩ I' = if I = I' then 1 else 0) ∧
  ∀ r, blkF Ψ p q K₀ r = none →
    detFac p r.2 (F.T r.1) * 1 = (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * F.υ r

def BaseGood (R : Subring Ω) (F : FrameD n J₀ Ω p q) : Prop :=
  (∀ k, xb A x₀ ⟨k, F.c k⟩ ≠ 0 ∧ ∀ i, xb A x₀ ⟨k, i⟩ / xb A x₀ ⟨k, F.c k⟩ ∈ R) ∧
  (∀ t I, F.u t I ∈ R ∧ F.u' I t ∈ R) ∧
  ∀ r, blkF Ψ p q K₀ r = none → F.υ r ≠ 0 ∧ F.υ r ∈ R ∧ (F.υ r)⁻¹ ∈ R

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ} (Z : Matrix (Fin r) (Fin r) Ω)
    (h : ∀ a b, Z a b ∈ R) : Z.det ∈ R := by
  let Z' : Matrix (Fin r) (Fin r) R := fun a b => ⟨Z a b, h a b⟩
  have e : Z = Z'.map R.subtype := by
    ext a b
    rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Z'.det).2

theorem mul_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {a b c : ℕ} {Y : Matrix (Fin a) (Fin b) Ω}
    {Z : Matrix (Fin b) (Fin c) Ω} (hY : ∀ i j, Y i j ∈ R) (hZ : ∀ i j, Z i j ∈ R) (i : Fin a) (j : Fin c) :
    (Y * Z) i j ∈ R := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => R.mul_mem (hY i k) (hZ k j)

theorem exists_left_inv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {κ : Type} {x : κ → Ω} {L : Lat ξ E} {r n m : ℕ} {φ : Fin n → Module.Dual Ω E}
    (hg : IsTwistGen ξ x L m φ) {q : Cpt ξ} {c : κ} (hc : InChart ξ x c q) {b : Fin r → E}
    (hb : L.IsFrameAt b q) (a : Fin r) :
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ q) ∧ ∀ k, ∑ j, g j * (φ j (b k) / x c ^ m) = if a = k then 1 else 0 := by
  classical
  have hbL : ∀ k, b k ∈ L q := fun k => by rw [hb.2]; exact Submodule.subset_span ⟨k, rfl⟩
  let Bs := Module.Basis.span hb.1
  obtain ⟨w, hw⟩ := LinearMap.exists_extend (Bs.coord a)
  have hwb : ∀ k, w (b k) = if a = k then 1 else 0 := fun k => by
    have h1 := LinearMap.congr_fun hw (Bs k)
    have h2 : ((Bs k : Submodule.span Ω (Set.range b)) : E) = b k := by
      rw [Module.Basis.span_apply]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h2] at h1
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]
  have hreg : ∀ e ∈ L q, w e ∈ regAt ξ q := fun e he => by
    rw [hb.2] at he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨k, rfl⟩ := he
      rw [hwb]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp
    | add e e' _ _ h1 h2 => simpa using add_mem h1 h2
    | smul t e _ h1 =>
      have : w (t • e) = (t : Ω) * w e := (w.map_smul (t : Ω) e)
      rw [this]
      exact mul_mem t.2 h1
  obtain ⟨g, hg1, hg2⟩ := hg.2 q c hc w hreg
  exact ⟨g, hg1, fun k => by rw [← hwb k, hg2 _ (hbL k)]⟩

theorem frame_of_cols {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {κ : Type} {x : κ → Ω} {L : Lat ξ E} {r n m : ℕ} {φ : Fin n → Module.Dual Ω E}
    (hg : IsTwistGen ξ x L m φ) {q : Cpt ξ} {c : κ} (hc : InChart ξ x c q) {b e : Fin r → E}
    (hb : L.IsFrameAt b q) (he : LinearIndependent Ω e)
    (hs : Submodule.span Ω (Set.range e) = Submodule.span Ω (Set.range b)) {T : Matrix (Fin r) (Fin r) Ω}
    (hT : ColFac (regAt ξ q) (Matrix.of (fun j a => φ j (e a)) * T) (x c ^ m)) :
    L.IsFrameAt (colFrame e T) q := by
  obtain ⟨U, U', hU, hU', hUU, hAT⟩ := hT
  have hX : x c ^ m ≠ 0 := pow_ne_zero _ hc.1
  have hbmem : ∀ k, b k ∈ Submodule.span Ω (Set.range e) := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hemem : ∀ k, e k ∈ Submodule.span Ω (Set.range b) := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbmem k)
  choose g hg' using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hemem k)
  let P : Matrix (Fin r) (Fin r) Ω := Matrix.of fun l k => f k l
  let Q : Matrix (Fin r) (Fin r) Ω := Matrix.of fun l k => g k l
  have hbP : colFrame e P = b := funext hf
  have heQ : colFrame b Q = e := funext hg'
  have hPQ : P * Q = 1 := by
    have h1 : colFrame e (P * Q) = colFrame e (1 : Matrix (Fin r) (Fin r) Ω) := by rw [colFrame_mul, hbP, heQ, colFrame_one]
    ext a k
    have h2 := Fintype.linearIndependent_iff.1 he (fun a => (P * Q) a k - (1 : Matrix (Fin r) (Fin r) Ω) a k)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.2 (congrFun h1 k)) a
    exact sub_eq_zero.1 h2
  let M := Q * T
  have hTM : T = P * M := by
    show T = P * (Q * T)
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hframe : colFrame e T = colFrame b M := by rw [hTM, colFrame_mul, hbP]
  let C : Matrix (Fin n) (Fin r) Ω := Matrix.of fun j k => φ j (b k) / x c ^ m
  have hbL : ∀ k, b k ∈ L q := fun k => by rw [hb.2]; exact Submodule.subset_span ⟨k, rfl⟩
  have hC : ∀ j k, C j k ∈ regAt ξ q := fun j k => hg.1 j q c hc (b k) (hbL k)
  have hAP : (Matrix.of (fun j a => φ j (e a))) * P = (x c ^ m) • C := by
    ext j k
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    show ∑ l, φ j (e l) * f k l = x c ^ m * (φ j (b k) / x c ^ m)
    rw [mul_div_cancel₀ _ hX, ← hf k, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul, mul_comm]
  choose G hGr hGC using fun a => exists_left_inv hg hc hb a
  let Gm : Matrix (Fin r) (Fin n) Ω := Matrix.of G
  have hGC' : Gm * C = 1 := by
    ext a k
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hGC a k
  have hCM : C * M = U := by
    have h1 : (x c ^ m) • (C * M) = (x c ^ m) • U := by
      rw [← Matrix.smul_mul, ← hAP, Matrix.mul_assoc, ← hTM, hAT]
    exact smul_right_injective _ hX h1
  have hMU : M = Gm * U := by rw [← hCM, ← Matrix.mul_assoc, hGC', Matrix.one_mul]
  have hMreg : ∀ a k, M a k ∈ regAt ξ q := fun a k => by
    rw [hMU]
    exact mul_entry_mem _ hGr hU a k
  have hDreg : ∀ a k, (U' * C) a k ∈ regAt ξ q := mul_entry_mem _ hU' hC
  have hdet : (U' * C).det * M.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_assoc, hCM, hUU, Matrix.det_one]
  have hu : unitAt ξ q M.det := by
    refine ⟨fun h0 => ?_, det_mem _ _ hMreg, ?_⟩
    · rw [h0, mul_zero] at hdet
      exact zero_ne_one hdet
    · rw [← eq_inv_of_mul_eq_one_left hdet]
      exact det_mem _ _ hDreg
  rw [hframe]
  exact isFrameAt_matrix_comb X Ω ξ E L r b q M hb hMreg hu

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem minorIJ_single {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (a b : Fin N) :
    minorIJ h {a} {b} = h a b := by
  unfold minorIJ
  rw [dif_pos (by simp)]
  haveI : Unique (Fin ({b} : Finset (Fin N)).card) := inferInstanceAs (Unique (Fin 1))
  rw [det_unique]
  show h _ _ = _
  congr 1
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

theorem sum_minor_single {R : Type} [CommRing R] {N : ℕ} (c : Finset (Fin N) → R) (M : Matrix (Fin N) (Fin N) R)
    (a₀ : Fin N) : ∑ I, c I * minorIJ M I {a₀} = ∑ a, c {a} * M a a₀ := by
  classical
  have himg : ∑ a, c {a} * M a a₀ =
      ∑ I ∈ Finset.univ.image (fun a : Fin N => ({a} : Finset (Fin N))), c I * minorIJ M I {a₀} := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
    exact Finset.sum_congr rfl fun a _ => by rw [minorIJ_single]
  rw [himg]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun I _ hI => ?_
  have hc : I.card ≠ ({a₀} : Finset (Fin N)).card := fun e => by
    rw [Finset.card_singleton] at e
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 e
    exact hI (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  rw [minorIJ, dif_neg hc, mul_zero]

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)

omit [Fintype Ψ] [Fintype K₀] in

theorem eq_fullW_iff (t : StepIx Ψ p q) (hk : ∀ r, blkF Ψ p q K₀ r ≠ some (.inr t)) (τ : Ψ) (hp : 0 < p) :
    (⟨.inr t, hk⟩ : NonPluckerBlocks (blkF Ψ p q K₀)) = fullW τ hp ↔ t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p := by
  constructor
  · intro e
    have e1 := Sum.inr_injective (congrArg Subtype.val e)
    rw [e1]
    exact ⟨rfl, by show p - 1 + 1 = p; omega⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, i⟩ := t
    obtain rfl : s = .inl τ := h1
    refine Subtype.ext (congrArg Sum.inr (congrArg (Sigma.mk _) (Fin.ext ?_)))
    show (i : ℕ) = p - 1
    have : (i : ℕ) + 1 = p := h2
    omega

omit [Fintype Ψ] [Fintype K₀] in

theorem eq_fullO_iff (t : StepIx Ψ p q) (hk : ∀ r, blkF Ψ p q K₀ r ≠ some (.inr t)) (τ : Ψ) (hq : 0 < q) :
    (⟨.inr t, hk⟩ : NonPluckerBlocks (blkF Ψ p q K₀)) = fullO τ hq ↔ t.1 = .inr τ ∧ (t.2 : ℕ) + 1 = q := by
  constructor
  · intro e
    have e1 := Sum.inr_injective (congrArg Subtype.val e)
    rw [e1]
    exact ⟨rfl, by show q - 1 + 1 = q; omega⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, i⟩ := t
    obtain rfl : s = .inr τ := h1
    refine Subtype.ext (congrArg Sum.inr (congrArg (Sigma.mk _) (Fin.ext ?_)))
    show (i : ℕ) = q - 1
    have : (i : ℕ) + 1 = q := h2
    omega

theorem twist_prod (F : FrameD n J₀ Ω p q) (r : Ψ × Fin (p + q)) :
    ∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k' =
      chartX x₀ F ^ wtOf m r * (if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (zW A x₀ F r.1 h.1)⁻¹ else 1) *
        (if h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q then (zO A x₀ F r.1 h.1)⁻¹ else 1) := by
  classical
  let G : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k => xb A x₀ ⟨k, F.c k⟩
  let f₁ : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k => if k.1.isLeft then G k ^ wtOf m r else 1
  let f₂ : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k =>
    if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (if k = fullW r.1 h.1 then (G k)⁻¹ else 1) else 1
  let f₃ : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k =>
    if h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q then (if k = fullO r.1 h.1 then (G k)⁻¹ else 1) else 1
  have hpt : ∀ k, G k ^ bF m r k = f₁ k * f₂ k * f₃ k := by
    rintro ⟨k₀ | t, hk⟩
    · have e2 : f₂ ⟨.inl k₀, hk⟩ = 1 := by
        show (if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (if _ = fullW r.1 h.1 then _ else 1) else 1) = 1
        split_ifs with h h'
        · exact absurd (congrArg Subtype.val h') (by simp [fullW])
        · rfl
        · rfl
      have e3 : f₃ ⟨.inl k₀, hk⟩ = 1 := by
        show (if h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q then (if _ = fullO r.1 h.1 then _ else 1) else 1) = 1
        split_ifs with h h'
        · exact absurd (congrArg Subtype.val h') (by simp [fullO])
        · rfl
        · rfl
      rw [e2, e3, mul_one, mul_one]
      show G _ ^ ((wtOf m r : ℕ) : ℤ) = if true = true then _ else _
      rw [zpow_natCast, if_pos rfl]
    · let c1 : Prop := t.1 = .inl r.1 ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (r.2 : ℕ) + 1
      let c2 : Prop := t.1 = .inr r.1 ∧ (t.2 : ℕ) + 1 = q ∧ (r.2 : ℕ) + 1 = p + q
      have e2 : f₂ ⟨.inr t, hk⟩ = if c1 then (G ⟨.inr t, hk⟩)⁻¹ else 1 := by
        show (if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (if _ = fullW r.1 h.1 then _ else 1) else 1) = _
        by_cases h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1
        · rw [dif_pos h]
          simp only [eq_fullW_iff t hk r.1 h.1, c1, h.2, and_true]
        · rw [dif_neg h, if_neg fun e => h ⟨by have := e.2.1; omega, e.2.2⟩]
      have e3 : f₃ ⟨.inr t, hk⟩ = if c2 then (G ⟨.inr t, hk⟩)⁻¹ else 1 := by
        show (if h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q then (if _ = fullO r.1 h.1 then _ else 1) else 1) = _
        by_cases h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q
        · rw [dif_pos h]
          simp only [eq_fullO_iff t hk r.1 h.1, c2, h.2, and_true]
        · rw [dif_neg h, if_neg fun e => h ⟨by have := e.2.1; omega, e.2.2⟩]
      have e1 : f₁ ⟨.inr t, hk⟩ = 1 := rfl
      have ht : bF m r ⟨.inr t, hk⟩ = -((if c1 then 1 else 0) + (if c2 then 1 else 0)) := rfl
      rw [e1, e2, e3, ht, one_mul]
      by_cases h1 : c1
      · have h2 : ¬ c2 := fun e => Sum.inl_ne_inr (h1.1.symm.trans e.1)
        simp [h1, h2]
      · by_cases h2 : c2
        · simp [h1, h2]
        · simp [h1, h2]
  have hinj : Function.Injective (inlB (Ψ := Ψ) (p := p) (q := q) (K₀ := K₀)) := fun a b e =>
    Sum.inl_injective (congrArg Subtype.val e)
  have e₁ : ∏ k, f₁ k = chartX x₀ F ^ wtOf m r := by
    rw [← Fintype.prod_of_injective inlB hinj (fun k₀ => G (inlB k₀) ^ wtOf m r) f₁ ?_ (fun k₀ => ?_), Finset.prod_pow]
    · rfl
    · rintro ⟨k₀ | t, hk⟩ hn
      · exact absurd ⟨k₀, rfl⟩ hn
      · rfl
    · exact (if_pos rfl).symm
  have e₂ : ∏ k, f₂ k = if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (zW A x₀ F r.1 h.1)⁻¹ else 1 := by
    by_cases h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1
    · simp only [f₂, dif_pos h]
      rw [Finset.prod_ite_eq' Finset.univ (fullW r.1 h.1) fun k => (G k)⁻¹, if_pos (Finset.mem_univ _)]
      rfl
    · simp only [f₂, dif_neg h, Finset.prod_const_one]
  have e₃ : ∏ k, f₃ k = if h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q then (zO A x₀ F r.1 h.1)⁻¹ else 1 := by
    by_cases h : 0 < q ∧ (r.2 : ℕ) + 1 = p + q
    · simp only [f₃, dif_pos h]
      rw [Finset.prod_ite_eq' Finset.univ (fullO r.1 h.1) fun k => (G k)⁻¹, if_pos (Finset.mem_univ _)]
      rfl
    · simp only [f₃, dif_neg h, Finset.prod_const_one]
  rw [← e₁, ← e₂, ← e₃, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => hpt k

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)

omit [Fintype Ψ] in
theorem posOf_injective (s : Ψ ⊕ Ψ) : Function.Injective (posOf (Ψ := Ψ) p q s) := by
  rcases s with τ | τ
  · exact (wEmb_strictMono p q).injective
  · exact (omEmb_strictMono p q).injective

omit [Fintype Ψ] in

theorem step_facts (r : Ψ × Fin (p + q)) (s : Ψ ⊕ Ψ) (i₀ : Fin (rk Ψ p q s)) (hi : (i₀ : ℕ) = 0)
    (hst : stepOf Ψ p q r = ⟨s, i₀⟩) :
    stepCols (p + q) p r.2 = {posOf p q s i₀} ∧
      (∀ b, posOf p q s b ∈ if (r.2 : ℕ) + 1 ≤ p then wIdx (p + q) p else omIdx (p + q) p) ∧
      ∀ a b, ((posOf p q s a : ℕ) < p + q - p ↔ (posOf p q s b : ℕ) < p + q - p) := by
  unfold stepOf at hst
  split_ifs at hst with hl
  · cases hst
    have hi' : (r.2 : ℕ) = 0 := hi
    refine ⟨?_, fun b => ?_, fun a b => ?_⟩
    · ext a
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [if_pos (by omega)]
      constructor
      · rintro ⟨h1, h2⟩
        refine Fin.ext ?_
        show (a : ℕ) = q + (r.2 : ℕ)
        omega
      · rintro rfl
        show p + q - p ≤ q + (r.2 : ℕ) ∧ q + (r.2 : ℕ) < p + q - p + ((r.2 : ℕ) + 1)
        omega
    · rw [if_pos (by omega)]
      exact (mem_wIdx_iff p q _).2 ⟨b, rfl⟩
    · show q + (a : ℕ) < p + q - p ↔ q + (b : ℕ) < p + q - p
      omega
  · cases hst
    have hi' : (r.2 : ℕ) - p = 0 := hi
    refine ⟨?_, fun b => ?_, fun a b => ?_⟩
    · ext a
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [if_neg (by omega)]
      constructor
      · intro h1
        refine Fin.ext ?_
        show (a : ℕ) = (r.2 : ℕ) - p
        omega
      · rintro rfl
        show (r.2 : ℕ) - p < (r.2 : ℕ) + 1 - p
        omega
    · rw [if_neg (by omega)]
      exact (mem_omIdx_iff p q _).2 ⟨b, rfl⟩
    · have ha := a.2
      have hb := b.2
      have ha' : (a : ℕ) < q := ha
      have hb' : (b : ℕ) < q := hb
      show (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p
      omega

theorem step_col (R : Subring Ω) (F : FrameD n J₀ Ω p q) (hF : FrameIds A x₀ m F) (hR : BaseGood A x₀ R F)
    (r : Ψ × Fin (p + q)) (s : Ψ ⊕ Ψ) (i₀ : Fin (rk Ψ p q s)) (hi : (i₀ : ℕ) = 0) (hst : stepOf Ψ p q r = ⟨s, i₀⟩)
    (hpr : IsProperStep (p + q) p r.2) :
    ColFac R (detFac p r.2 (F.T r.1) • (A s * (F.T r.1).submatrix (posOf p q s) (posOf p q s)))
      (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') := by
  classical
  have hblk : blkF Ψ p q K₀ r = some (.inr ⟨s, i₀⟩) := by
    unfold blkF
    rw [if_pos hpr, hst]
  obtain ⟨hcols, hmem, hsame⟩ := step_facts r s i₀ hi hst
  have hrows : ∀ b, IsStepRows (p + q) p r.2 {posOf p q s b} := fun b =>
    ⟨by rw [hcols]; simp, Finset.singleton_subset_iff.2 (hmem b)⟩
  let ci : Fin (n s) → idx (p := p) (q := q) J₀ n (.inr ⟨s, i₀⟩) := fun j _ => j
  let U : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω :=
    Matrix.of fun j b => F.u ⟨.inr ⟨s, i₀⟩, ci j⟩ {posOf p q s b}
  let U' : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω :=
    Matrix.of fun b j => F.u' {posOf p q s b} ⟨.inr ⟨s, i₀⟩, ci j⟩
  refine ⟨U, U', fun i j => (hR.2.1 _ _).1, fun i j => (hR.2.1 _ _).2, ?_, ?_⟩
  · ext b b'
    have hsum := hF.2.2.1 r _ hblk {posOf p q s b} {posOf p q s b'} (hrows b) (hrows b')
    let ev : idx (p := p) (q := q) J₀ n (.inr ⟨s, i₀⟩) → Fin (n s) := fun i =>
      (show Fin ((i₀ : ℕ) + 1) → Fin (n s) from i) ⟨0, by omega⟩
    let e : Fin (n s) ≃ idx (p := p) (q := q) J₀ n (.inr ⟨s, i₀⟩) :=
      { toFun := ci
        invFun := ev
        left_inv := fun _ => rfl
        right_inv := fun i => funext fun a => congrArg (show Fin ((i₀ : ℕ) + 1) → Fin (n s) from i)
          (Fin.ext (by
            have h' : (a : ℕ) < (i₀ : ℕ) + 1 := a.2
            show 0 = (a : ℕ)
            omega)) }
    have h1 : ∑ j, U' b j * U j b' = ∑ i : idx (p := p) (q := q) J₀ n (.inr ⟨s, i₀⟩),
        F.u' {posOf p q s b} ⟨.inr ⟨s, i₀⟩, i⟩ * F.u ⟨.inr ⟨s, i₀⟩, i⟩ {posOf p q s b'} :=
      Fintype.sum_equiv e _ _ fun j => rfl
    rw [Matrix.mul_apply, h1, hsum, Matrix.one_apply]
    simp only [Finset.singleton_inj, (posOf_injective s).eq_iff]
  · ext j b
    let h : Matrix (Fin (p + q)) (Fin (p + q)) Ω := Matrix.single (posOf p q s b) (posOf p q s i₀) 1
    have hh : ∀ a, h a (posOf p q s i₀) = if a = posOf p q s b then 1 else 0 := fun a => by
      simp [h, Matrix.single_apply, eq_comm]
    have hblock : IsBlockDiag p h := fun a c hac => by
      simp only [h, Matrix.single_apply]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hac (hsame _ _)
    have hid := hF.2.1 r _ hblk (ci j) h hblock
    rw [hcols, sum_minor_single, sum_minor_single] at hid
    have hcoef : ∀ a, coefF A ⟨.inr ⟨s, i₀⟩, ci j⟩ {a} = aExt A s j a := fun a => by
      show (if e : ({a} : Finset (Fin (p + q))).card = (i₀ : ℕ) + 1 then
        ((aExt A s).submatrix (ci j) (({a} : Finset (Fin (p + q))).orderEmbOfFin e)).det else 0) = _
      rw [dif_pos (by simp [hi]), Matrix.det_eq_elem_of_card_eq_one (by simp [hi]) ⟨0, by omega⟩]
      show aExt A s j _ = _
      congr 1
      exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
    have hTh : ∀ a, (F.T r.1 * h) a (posOf p q s i₀) = F.T r.1 a (posOf p q s b) := fun a => by
      rw [Matrix.mul_apply, Finset.sum_eq_single (posOf p q s b) (fun c _ hc => by rw [hh, if_neg hc, mul_zero])
        (by simp), hh, if_pos rfl, mul_one]
    have hL : ∑ a, coefF A ⟨.inr ⟨s, i₀⟩, ci j⟩ {a} * (F.T r.1 * h) a (posOf p q s i₀) =
        (A s * (F.T r.1).submatrix (posOf p q s) (posOf p q s)) j b := by
      simp only [hcoef, hTh, aExt, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    have hRr : ∑ a, F.u ⟨.inr ⟨s, i₀⟩, ci j⟩ {a} * h a (posOf p q s i₀) = U j b := by
      simp only [hh, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [U]
    rw [hL, hRr] at hid
    simpa [Matrix.smul_apply] using hid

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem ColFac.rescale {Ω : Type} [Field Ω] {R : Subring Ω} {a b : ℕ} {M : Matrix (Fin a) (Fin b) Ω} {X c v : Ω}
    (hc : c ≠ 0) (hv : v ≠ 0) (hvR : v ∈ R) (hvi : v⁻¹ ∈ R) (h : ColFac R ((c * v) • M) (c * X)) : ColFac R M X := by
  obtain ⟨U, U', hU, hU', hUU, e⟩ := h
  refine ⟨v⁻¹ • U, v • U', fun i j => R.mul_mem hvi (hU i j), fun i j => R.mul_mem hvR (hU' i j), ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hv, one_smul, hUU]
  · have h0 : c * v ≠ 0 := mul_ne_zero hc hv
    have : M = (c * v)⁻¹ • ((c * X) • U) := by rw [← e, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [this, smul_smul, smul_smul]
    congr 1
    field_simp

theorem ColFac.line {Ω : Type} [Field Ω] {R : Subring Ω} {a r : ℕ} (hr : r = 1) (M : Matrix (Fin a) (Fin r) Ω)
    (T : Matrix (Fin r) (Fin r) Ω) (i₀ : Fin r) (j₀ : Fin a) (hz : M j₀ i₀ ≠ 0) (hrat : ∀ j, M j i₀ / M j₀ i₀ ∈ R)
    {X v : Ω} (hv : v ≠ 0) (hvR : v ∈ R) (hvi : v⁻¹ ∈ R) (h : T i₀ i₀ * M j₀ i₀ = X * v) :
    ColFac R (M * T) X := by
  subst hr
  have hi : ∀ i : Fin 1, i = i₀ := fun i => Subsingleton.elim _ _
  refine ⟨Matrix.of fun j _ => M j i₀ / M j₀ i₀ * v, Matrix.of fun _ j => if j = j₀ then v⁻¹ else 0,
    fun j _ => R.mul_mem (hrat j) hvR, fun _ j => ?_, ?_, ?_⟩
  · show (if j = j₀ then v⁻¹ else 0) ∈ R
    split_ifs
    · exact hvi
    · exact R.zero_mem
  · ext b b'
    rw [Matrix.mul_apply, Finset.sum_eq_single j₀ (fun j _ hj => by simp [hj]) (by simp)]
    rw [hi b, hi b']
    simp [hz, hv]
  · ext j b
    have hT : T i₀ i₀ = X * v / M j₀ i₀ := eq_div_of_mul_eq hz h
    rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.smul_apply, hi default, hi b, smul_eq_mul, hT]
    show _ = X * (M j i₀ / M j₀ i₀ * v)
    field_simp

theorem frame_unmap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E E' : Type}
    [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] {f : E →ₗ[Ω] E'} (hf : Function.Injective f)
    {L : Lat ξ E} {r : ℕ} {b : Fin r → E} {q : Cpt ξ} (h : (L.map f).IsFrameAt (fun a => f (b a)) q) :
    L.IsFrameAt b q := by
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have h2 := h.2
  refine Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ q)) hf ?_
  refine h2.trans ?_
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {x₀ : (Σ k, J₀ k) → Ω} {m : Ψ ⊕ Ψ → ℕ}

theorem detFac_eq {i : Fin (p + q)} (T : Matrix (Fin (p + q)) (Fin (p + q)) Ω) :
    detFac p i T = (if p ≤ (i : ℕ) + 1 then (wBlock T).det else 1) *
      if (i : ℕ) + 1 = p + q then (omBlock T).det else 1 := by
  unfold detFac
  rw [minorIJ_wIdx, minorIJ_omIdx]

variable (A x₀) in

def aW (F : FrameD n J₀ Ω p q) (τ : Ψ) : Ω := if h : 0 < p then (zW A x₀ F τ h)⁻¹ else 1

theorem aW_eq (F : FrameD n J₀ Ω p q) (r : Ψ × Fin (p + q)) (h : p ≤ (r.2 : ℕ) + 1) :
    (if h : 0 < p ∧ p ≤ (r.2 : ℕ) + 1 then (zW A x₀ F r.1 h.1)⁻¹ else 1) = aW A x₀ F r.1 := by
  unfold aW
  by_cases h0 : 0 < p
  · rw [dif_pos ⟨h0, h⟩, dif_pos h0]
  · rw [dif_neg fun e => h0 e.1, dif_neg h0]

theorem chartX_ne {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hR : BaseGood A x₀ R F) : chartX x₀ F ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k₀ _ => (hR.1 (inlB k₀)).1

theorem zW_ne {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hR : BaseGood A x₀ R F) (τ : Ψ) (h : 0 < p) :
    zW A x₀ F τ h ≠ 0 := (hR.1 _).1

theorem zO_ne {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hR : BaseGood A x₀ R F) (τ : Ψ) (h : 0 < q) :
    zO A x₀ F τ h ≠ 0 := (hR.1 _).1

theorem aW_ne {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hR : BaseGood A x₀ R F) (τ : Ψ) : aW A x₀ F τ ≠ 0 := by
  unfold aW
  split_ifs with h
  · exact inv_ne_zero (zW_ne hR τ h)
  · exact one_ne_zero

theorem xv_line (t : StepIx Ψ p q) (ht : (t.2 : ℕ) = 0) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1))
    (a : Fin ((t.2 : ℕ) + 1)) : xv A x₀ ⟨.inr t, J⟩ = A t.1 (J a) (Fin.castLE t.2.2 a) :=
  Matrix.det_eq_elem_of_card_eq_one (by simp [ht]) a

theorem detW {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hF : FrameIds A x₀ m F) (hR : BaseGood A x₀ R F) (τ : Ψ) :
    ∃ v : Ω, v ≠ 0 ∧ v ∈ R ∧ v⁻¹ ∈ R ∧
      (wBlock (F.T τ)).det = chartX x₀ F ^ (p * m (.inl τ)) * aW A x₀ F τ * v := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, one_ne_zero, R.one_mem, by simpa using R.one_mem, ?_⟩
    simp [aW]
  let r : Ψ × Fin (p + q) := (τ, ⟨p - 1, by omega⟩)
  have hr : (r.2 : ℕ) + 1 = p := by show p - 1 + 1 = p; omega
  have hn : blkF Ψ p q K₀ r = none := if_neg fun e => e.1 hr
  obtain ⟨h0, h1, h2⟩ := hR.2.2 r hn
  refine ⟨F.υ r, h0, h1, h2, ?_⟩
  have h := hF.2.2.2 r hn
  have hw : wtOf m r = p * m (.inl τ) := by
    have a1 : rkW r.2 = p := by unfold rkW; omega
    have a2 : rkO r.2 = 0 := by unfold rkO; omega
    unfold wtOf
    rw [a1, a2, zero_mul, add_zero]
  have ho : (if (r.2 : ℕ) + 1 = p + q then (omBlock (F.T r.1)).det else 1) = 1 := by
    split_ifs with e
    · have hq : q = 0 := by omega
      haveI : IsEmpty (Fin q) := by rw [hq]; infer_instance
      exact Matrix.det_isEmpty
    · rfl
  rw [mul_one, detFac_eq, ho, mul_one, if_pos hr.ge, twist_prod, aW_eq F r hr.ge, dif_neg (fun e => by omega), mul_one,
    hw] at h
  exact h

theorem colW {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hF : FrameIds A x₀ m F) (hR : BaseGood A x₀ R F) (τ : Ψ)
    (hp : 0 < p) : ColFac R (A (.inl τ) * (F.T τ).submatrix (posOf p q (.inl τ)) (posOf p q (.inl τ)))
      (chartX x₀ F ^ m (.inl τ)) := by
  rcases Nat.lt_or_ge 1 p with h2 | h1
  · let r : Ψ × Fin (p + q) := (τ, ⟨0, by omega⟩)
    have hpr : IsProperStep (p + q) p r.2 := ⟨by show 0 + 1 ≠ p; omega, by show 0 + 1 ≠ p + q; omega⟩
    have hst : stepOf Ψ p q r = ⟨.inl τ, ⟨0, hp⟩⟩ := dif_pos hp
    have h := step_col A x₀ m R F hF hR r (.inl τ) ⟨0, hp⟩ rfl hst hpr
    have hw : wtOf m r = m (.inl τ) := by
      have a1 : rkW r.2 = 1 := by show min (0 + 1) p = 1; omega
      have a2 : rkO r.2 = 0 := by show 0 + 1 - min (0 + 1) p = 0; omega
      unfold wtOf
      rw [a1, a2, zero_mul, add_zero, one_mul]
    have e1 : ¬ p ≤ (r.2 : ℕ) + 1 := by show ¬ p ≤ 0 + 1; omega
    have e2 : ¬ (r.2 : ℕ) + 1 = p + q := by show ¬ 0 + 1 = p + q; omega
    rw [twist_prod, detFac_eq, if_neg e1, if_neg e2, dif_neg (fun e => e1 e.2), dif_neg (fun e => e2 e.2), hw] at h
    simp only [mul_one, one_smul] at h
    exact h
  · have hp1 : p = 1 := by omega
    obtain ⟨v, h0, hvR, hvi, e⟩ := detW hF hR τ (m := m)
    let t : StepIx Ψ p q := ⟨.inl τ, ⟨p - 1, by show p - 1 < p; omega⟩⟩
    have ht : (t.2 : ℕ) = 0 := by show p - 1 = 0; omega
    let a : Fin ((t.2 : ℕ) + 1) := ⟨0, by omega⟩
    let J : Fin ((t.2 : ℕ) + 1) → Fin (n (.inl τ)) := F.c (fullW τ hp)
    have hz : ∀ i : Fin ((t.2 : ℕ) + 1) → Fin (n (.inl τ)),
        xb A x₀ ⟨fullW τ hp, i⟩ = A (.inl τ) (i a) ⟨0, hp⟩ := fun i => xv_line t ht i a
    refine ColFac.line hp1 (A (.inl τ)) _ ⟨0, hp⟩ (J a) ?_ ?_ h0 hvR hvi ?_
    · exact fun e0 => zW_ne hR τ hp ((hz J).trans e0)
    · intro j
      have := (hR.1 (fullW τ hp)).2 (fun _ => j)
      rwa [hz (fun _ => j), show xb A x₀ ⟨fullW τ hp, F.c (fullW τ hp)⟩ = A (.inl τ) (J a) ⟨0, hp⟩ from hz J] at this
    · have hd : (wBlock (F.T τ)).det = wBlock (F.T τ) ⟨0, hp⟩ ⟨0, hp⟩ :=
        Matrix.det_eq_elem_of_card_eq_one (by simp [hp1]) _
      have hzz : A (.inl τ) (J a) ⟨0, hp⟩ = zW A x₀ F τ hp := (hz J).symm
      show wBlock (F.T τ) ⟨0, hp⟩ ⟨0, hp⟩ * A (.inl τ) (J a) ⟨0, hp⟩ = _
      have hpw : chartX x₀ F ^ (p * m (.inl τ)) = chartX x₀ F ^ m (.inl τ) := by
        congr 1
        rw [hp1, one_mul]
      rw [← hd, e, hzz, show aW A x₀ F τ = (zW A x₀ F τ hp)⁻¹ from dif_pos hp, hpw]
      have := zW_ne hR τ hp
      field_simp

theorem colO {R : Subring Ω} {F : FrameD n J₀ Ω p q} (hF : FrameIds A x₀ m F) (hR : BaseGood A x₀ R F) (τ : Ψ)
    (hq : 0 < q) : ColFac R (A (.inr τ) * (F.T τ).submatrix (posOf p q (.inr τ)) (posOf p q (.inr τ)))
      (chartX x₀ F ^ m (.inr τ)) := by
  obtain ⟨v, h0, hvR, hvi, e⟩ := detW hF hR τ (m := m)
  let r : Ψ × Fin (p + q) := (τ, ⟨p, by omega⟩)
  have hw : wtOf m r = p * m (.inl τ) + m (.inr τ) := by
    have a1 : rkW r.2 = p := by show min (p + 1) p = p; omega
    have a2 : rkO r.2 = 1 := by show p + 1 - min (p + 1) p = 1; omega
    unfold wtOf
    rw [a1, a2, one_mul]
  have hle : p ≤ (r.2 : ℕ) + 1 := by show p ≤ p + 1; omega
  have hc : chartX x₀ F ^ (p * m (.inl τ)) * aW A x₀ F τ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (chartX_ne hR)) (aW_ne hR τ)
  by_cases h2 : 2 ≤ q
  · have e2 : ¬ (r.2 : ℕ) + 1 = p + q := by show ¬ p + 1 = p + q; omega
    have hpr : IsProperStep (p + q) p r.2 := ⟨by show p + 1 ≠ p; omega, e2⟩
    have hst : stepOf Ψ p q r = ⟨.inr τ, ⟨0, hq⟩⟩ := by
      unfold stepOf
      rw [dif_neg (by show ¬ p < p; omega)]
      simp [r]
    have h := step_col A x₀ m R F hF hR r (.inr τ) ⟨0, hq⟩ rfl hst hpr
    rw [twist_prod, detFac_eq, if_pos hle, if_neg e2, aW_eq F r hle, dif_neg (fun e => e2 e.2), hw, mul_one, mul_one,
      show r.1 = τ from rfl, e, pow_add] at h
    refine ColFac.rescale hc h0 hvR hvi ?_
    convert h using 1
    ring
  · have hq1 : q = 1 := by omega
    have e2 : (r.2 : ℕ) + 1 = p + q := by show p + 1 = p + q; omega
    have hn : blkF Ψ p q K₀ r = none := if_neg fun e => e.2 e2
    obtain ⟨u0, uR, ui⟩ := hR.2.2 r hn
    have h := hF.2.2.2 r hn
    rw [mul_one, detFac_eq, if_pos hle, if_pos e2, twist_prod, aW_eq F r hle, dif_pos ⟨hq, e2⟩, hw,
      show r.1 = τ from rfl, e, pow_add] at h
    let t : StepIx Ψ p q := ⟨.inr τ, ⟨q - 1, by show q - 1 < q; omega⟩⟩
    have ht : (t.2 : ℕ) = 0 := by show q - 1 = 0; omega
    let a : Fin ((t.2 : ℕ) + 1) := ⟨0, by omega⟩
    let J : Fin ((t.2 : ℕ) + 1) → Fin (n (.inr τ)) := F.c (fullO τ hq)
    have hz : ∀ i : Fin ((t.2 : ℕ) + 1) → Fin (n (.inr τ)),
        xb A x₀ ⟨fullO τ hq, i⟩ = A (.inr τ) (i a) ⟨0, hq⟩ := fun i => xv_line t ht i a
    refine ColFac.line hq1 (A (.inr τ)) _ ⟨0, hq⟩ (J a) ?_ ?_
      (mul_ne_zero u0 (inv_ne_zero h0)) (R.mul_mem uR hvi) ?_ ?_
    · exact fun e0 => zO_ne hR τ hq ((hz J).trans e0)
    · intro j
      have := (hR.1 (fullO τ hq)).2 (fun _ => j)
      rwa [hz (fun _ => j), show xb A x₀ ⟨fullO τ hq, F.c (fullO τ hq)⟩ = A (.inr τ) (J a) ⟨0, hq⟩ from hz J] at this
    · rw [mul_inv, inv_inv]
      exact R.mul_mem ui hvR
    · have hd : (omBlock (F.T τ)).det = omBlock (F.T τ) ⟨0, hq⟩ ⟨0, hq⟩ :=
        Matrix.det_eq_elem_of_card_eq_one (by simp [hq1]) _
      have hzz : A (.inr τ) (J a) ⟨0, hq⟩ = zO A x₀ F τ hq := (hz J).symm
      show omBlock (F.T τ) ⟨0, hq⟩ ⟨0, hq⟩ * A (.inr τ) (J a) ⟨0, hq⟩ = _
      rw [← hd, hzz]
      have hzn := zO_ne hR τ hq
      have h' : v * (omBlock (F.T τ)).det =
          chartX x₀ F ^ m (.inr τ) * (zO A x₀ F τ hq)⁻¹ * F.υ r :=
        mul_left_cancel₀ hc (by linear_combination h)
      field_simp
      field_simp at h'
      linear_combination h'

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) := LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  intro a b h
  have h2 := congrArg (fun z : EE A => z.2 τ) h
  simpa [inO] using h2

theorem isFrameAt_of_goodAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hforms htie h q F hF hG τ
  have hF' : FrameIds (aOf 𝔐 bW bO φ) x₀ m F := hF
  have hch := (inBlockChart_iff_X_notMem htie q F.c).2 hG.1
  have hR : BaseGood (aOf 𝔐 bW bO φ) x₀ (regAt 𝔐.ξ q) F :=
    ⟨fun k => hch k, fun t I => ⟨RegAt.mem_regAt htie (hG.2.1 t I).1, RegAt.mem_regAt htie (hG.2.1 t I).2⟩,
      fun r hr => ⟨(hG.2.2 r hr).1, RegAt.mem_regAt htie (hG.2.2 r hr).2.1,
        RegAt.mem_regAt htie (hG.2.2 r hr).2.2⟩⟩
  have hc : InChart 𝔐.ξ (seg x₀) (c₀ F) q := by
    refine ⟨chartX_ne hR, fun c' => ?_⟩
    show (∏ k, x₀ ⟨k, c' k⟩) / (∏ k, x₀ ⟨k, c₀ F k⟩) ∈ regAt 𝔐.ξ q
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => (hR.1 (inlB k)).2 (c' k)
  obtain ⟨hvb, hbas, htw, -⟩ := hforms
  have key : ∀ (s : CMType H ⊕ CMType H) (T : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (rk (CMType H) D.p D.q s)) Ω),
      (rk (CMType H) D.p D.q s = 0 ∨ ColFac (regAt 𝔐.ξ q) (aOf 𝔐 bW bO φ s * T) (chartX x₀ F ^ m s)) →
      (LL 𝔐 s).IsFrameAt (colFrame (cc 𝔐 bW bO s) T) q := by
    intro s T hT
    obtain ⟨U, hU, b, hb, hf⟩ := hvb s q (Set.mem_univ _)
    have hfr := hf q (Set.mem_univ _) hU
    rcases hT with h0 | hT
    · have : colFrame (cc 𝔐 bW bO s) T = b := funext fun a => absurd a.2 (by omega)
      rw [this]
      exact hfr
    · exact frame_of_cols (htw s) hc hfr (hbas s).1 ((hbas s).2.trans hb.symm) hT
  constructor
  · have h1 := key (.inl τ) (wBlock (F.T τ)) (by
      rcases Nat.eq_zero_or_pos D.p with h0 | hp
      · exact .inl h0
      · exact .inr (colW hF' hR τ hp))
    have e : (fun b => inW 𝔐 (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ)) b)) =
        colFrame (cc 𝔐 bW bO (.inl τ)) (wBlock (F.T τ)) := by
      funext b
      unfold colFrame
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => map_smul _ _ _
    refine frame_unmap (inW_injective 𝔐) ?_
    rw [e]
    exact h1
  · have h1 := key (.inr τ) (omBlock (F.T τ)) (by
      rcases Nat.eq_zero_or_pos D.q with h0 | hq
      · exact .inl h0
      · exact .inr (colO hF' hR τ hq))
    have e : (fun b => inO 𝔐 τ (colFrame (bO τ) (omBlock (F.T τ)) b)) =
        colFrame (cc 𝔐 bW bO (.inr τ)) (omBlock (F.T τ)) := by
      funext b
      unfold colFrame
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => map_smul _ _ _
    refine frame_unmap (inO_injective 𝔐 τ) ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt
