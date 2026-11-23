import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw

namespace GlobalTheory.LocSW

section Columns

variable (A : Type) [CommRing A] (n : ℕ)

def columnBlock : Matrix (Fin (n + n)) (Fin n) A :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) A) (0 : Matrix (Fin n) (Fin n) A)).submatrix finSumFinEquiv.symm id

def colX : Matrix (Fin (n + n)) (Fin n) A :=
  (Matrix.fromRows (0 : Matrix (Fin n) (Fin n) A) (1 : Matrix (Fin n) (Fin n) A)).submatrix finSumFinEquiv.symm id

variable {A n}

theorem blockMatrix_mul_blockColumn {k : Type} (a b c d : Matrix (Fin n) (Fin n) A) (x y : Matrix (Fin n) k A) :
    StdUnn.blk4 a b c d * (Matrix.fromRows x y).submatrix finSumFinEquiv.symm id =
      (Matrix.fromRows (a * x + b * y) (c * x + d * y)).submatrix finSumFinEquiv.symm id := by
  rw [StdUnn.blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]

theorem colY_mul {k : Type} (t : Matrix (Fin n) k A) :
    columnBlock A n * t = (Matrix.fromRows t (0 : Matrix (Fin n) k A)).submatrix finSumFinEquiv.symm id := by
  rw [columnBlock, ← Matrix.submatrix_id_id t, ← Equiv.coe_refl, Matrix.submatrix_mul_equiv, Matrix.fromRows_mul]
  simp

theorem col_form {k k' : Type} (x y : Matrix (Fin n) k A) (x' y' : Matrix (Fin n) k' A) :
    ((Matrix.fromRows x y).submatrix finSumFinEquiv.symm id)ᵀ *
      (StdUnn.blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) A) *
      (Matrix.fromRows x' y').submatrix finSumFinEquiv.symm id = xᵀ * y' - yᵀ * x' := by
  rw [Matrix.mul_assoc, blockMatrix_mul_blockColumn, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem colY_map {B : Type} [CommRing B] {Φ : Type} [FunLike Φ A B] [RingHomClass Φ A B] (f : Φ) :
    (columnBlock A n).map f = columnBlock B n := by
  rw [columnBlock, ← Matrix.submatrix_map, Matrix.fromRows_map, Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_zero _ (map_zero f), columnBlock]

theorem colX_map {B : Type} [CommRing B] {Φ : Type} [FunLike Φ A B] [RingHomClass Φ A B] (f : Φ) :
    (colX A n).map f = colX B n := by
  rw [colX, ← Matrix.submatrix_map, Matrix.fromRows_map, Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_zero _ (map_zero f), colX]

theorem isLagr_colY_blk {R : Type} [CommRing R] [Algebra R A] (c : A →ₐ[R] A) :
    IsLagr c (StdUnn.blk4 0 1 (-1) 0) (columnBlock A n) := by
  have e : Matrix.fromCols (columnBlock A n) (colX A n) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A).submatrix finSumFinEquiv.symm id := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [columnBlock, colX, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply,
        Matrix.zero_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
  refine ⟨?_, colX A n, (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A).submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · rw [colY_map, columnBlock, col_form]; simp
  · rw [colX_map, colX, col_form]; simp
  · rw [e, ← Equiv.coe_refl, Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_one_equiv]
  · rw [e, Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]

end Columns

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

def conjR : R ⊗[F] E →ₐ[R] R ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id R R) σ

@[simp] theorem conjR_tmul (r : R) (e : E) : conjR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := rfl

theorem conjR_eq_sigR (z : R ⊗[F] E) : conjR R σ z = sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_conjR {α β : Type} (M : Matrix α β (R ⊗[F] E)) : M.map (conjR R σ) = M.map (sigR R σ) :=
  Matrix.ext fun _ _ => conjR_eq_sigR R σ _

theorem UG_eq_HR (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : UG (conjR R σ) (JR R Q) = HR R σ Q := by
  have hJ : (JR (F := F) R Q)ᵀ = -JR R Q := by
    rw [JR_eq R hQ, StdUnn.blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
    change _ = (-Matrix.fromBlocks 0 1 (-1) 0).submatrix _ _
    rw [Matrix.fromBlocks_neg]
    simp
  ext g
  change (g.1)ᵀ * JR R Q * (g.1).map (conjR R σ) = JR R Q ↔ cT (sigR R σ) g.1 * JR R Q * g.1 = JR R Q
  rw [map_conjR, cT]
  constructor <;> intro h <;> have := congrArg Matrix.transpose h <;>
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, hJ] using this

def toUG (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : HA R σ Q ≃* UG (conjR R σ) (JR R Q) :=
  MulEquiv.subgroupCongr (UG_eq_HR R σ hQ).symm

variable {R σ}

@[simp] theorem coe_toUG (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (g : HA R σ Q) :
    ((toUG R σ hQ g : GL (Fin (n + n)) (R ⊗[F] E)) : Matrix _ _ _) = matR R σ g := rfl

@[simp] theorem matR_toUG_symm (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (g : UG (conjR R σ) (JR R Q)) :
    matR R σ ((toUG R σ hQ).symm g) = ((g : GL (Fin (n + n)) (R ⊗[F] E)) : Matrix _ _ _) := rfl

theorem continuous_toUG [TopologicalSpace R] (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : Continuous (toUG R σ hQ) :=
  (isEmbedding_matHom R σ Q).continuous.subtype_mk _

variable (R σ) in

theorem isLagr_colY (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : IsLagr (conjR R σ) (JR R Q) (columnBlock (R ⊗[F] E) n) := by
  rw [JR_eq R hQ]; exact isLagr_colY_blk _

theorem matR_mul_colY (p : upperParabolic R σ Q) :
    matR R σ p.1 * columnBlock (R ⊗[F] E) n = columnBlock (R ⊗[F] E) n * (leviUp R σ Q p : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  obtain ⟨a, b, c, d, e⟩ := exists_blockMatrixTwoByTwoFin_eq (matR R σ p.1)
  obtain rfl : c = 0 := Matrix.ext fun i j => by
    have := lower_eq_zero p.2 i j
    rwa [e, StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  rw [colY_mul, coe_leviUp, e, upperLeft_blockMatrix, columnBlock, blockMatrix_mul_blockColumn]
  simp

end Group

section Finite

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (om : G →* Module.End ℂ V) (K : Subgroup G)

theorem kFin_iff (φ : V) : FiniteDimensional ℂ (Submodule.span ℂ {φ' | ∃ k ∈ K, φ' = om k φ}) ↔
    ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ ∀ k ∈ K, om k φ ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

def kFin : Submodule ℂ V where
  carrier := {φ | φ ∈ S ∧ FiniteDimensional ℂ (Submodule.span ℂ {φ' | ∃ k ∈ K, φ' = om k φ})}
  zero_mem' := ⟨zero_mem _, (kFin_iff om K _).2 ⟨⊥, inferInstance, fun k _ => by simp⟩⟩
  add_mem' := fun {φ φ'} h h' => ⟨add_mem h.1 h'.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    obtain ⟨W', _, hW'⟩ := (kFin_iff om K _).1 h'.2
    exact (kFin_iff om K _).2 ⟨W ⊔ W', inferInstance, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩⟩
  smul_mem' := fun c φ h => ⟨Submodule.smul_mem _ c h.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    exact (kFin_iff om K _).2 ⟨W, inferInstance, fun k hk => by rw [map_smul]; exact W.smul_mem c (hW k hk)⟩⟩

def coefMap (l : V →ₗ[ℂ] ℂ) : V →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun g => l ∘ₗ om g

variable {S om K}

@[simp] theorem coefMap_apply (l : V →ₗ[ℂ] ℂ) (φ : V) (g : G) : coefMap om l φ g = l (om g φ) := rfl

theorem coefMap_om (l : V →ₗ[ℂ] ℂ) (φ : V) (h : G) : coefMap om l (om h φ) = fun g => coefMap om l φ (g * h) := by
  funext g
  rw [coefMap_apply, coefMap_apply, map_mul, Module.End.mul_apply]

theorem mem_kFin_of_isLocallyConstant [TopologicalSpace G] (hK : IsCompact (K : Set G)) {φ : V} (hφ : φ ∈ S)
    (h : IsLocallyConstant fun g => om g φ) : φ ∈ kFin S om K := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hf := (h.comp_continuous (continuous_subtype_val : Continuous fun k : K => (k : G))).range_finite
  exact ⟨hφ, (kFin_iff om K _).2 ⟨_, FiniteDimensional.span_of_finite ℂ hf, fun k hk =>
    Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩⟩⟩

end Finite

section Model

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)]
  (σ : E →ₐ[F] E) {n m : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

abbrev LocDbx (JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (κ : Type) [Fintype κ] :
    Type := Darboux (symp (R := R) (conjR R σ) (-1) JA (JR R Q)) κ

def IsLocModel (C : TestClass R) (ψ : AddChar R ℂ) (JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (χ : (R ⊗[F] E)ˣ →* Circle)
    {κ : Type} [Fintype κ] (d : LocDbx σ JA Q κ) (om : UG (conjR R σ) (JR R Q) →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsSplitting C ψ d (actB (conjR R σ)) om ∧
    SiegelRule (conjR R σ) C ψ (-1) JA (JR R Q) d χ (columnBlock (R ⊗[F] E) n) om

def IsYAdm (C : TestClass R) (ψ : AddChar R ℂ) {JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)} {κ : Type} [Fintype κ]
    (d : LocDbx σ JA Q κ) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  l ∈ C.adm κ ∧ ∀ z : Matrix (Fin m) (Fin n) (R ⊗[F] E), ∀ φ ∈ C.sp κ, l (d.rho ψ (z * (columnBlock (R ⊗[F] E) n)ᵀ) φ) = l φ

def secOf (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (C : TestClass R) {κ : Type} [Fintype κ]
    (om : UG (conjR R σ) (JR R Q) →* Module.End ℂ ((κ → R) → ℂ)) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) (K : Subgroup (HA R σ Q)) :
    Submodule ℂ (HA R σ Q → ℂ) :=
  (kFin (C.sp κ) (om.comp (toUG R σ hQ).toMonoidHom) K).map (coefMap (om.comp (toUG R σ hQ).toMonoidHom) l)

def secLoc (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (C : TestClass R) (ψ : AddChar R ℂ) (JA : Matrix (Fin m) (Fin m) (R ⊗[F] E))
    (χ : (R ⊗[F] E)ˣ →* Circle) (K : Subgroup (HA R σ Q)) : Submodule ℂ (HA R σ Q → ℂ) :=
  Submodule.span ℂ {f | ∃ (κ : Type) (_ : Fintype κ) (d : LocDbx σ JA Q κ)
    (om : UG (conjR R σ) (JR R Q) →* Module.End ℂ ((κ → R) → ℂ)) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ),
    IsLocModel σ C ψ JA χ d om ∧ IsYAdm σ C ψ d l ∧ f ∈ secOf σ hQ C om l K}

variable (F E) in

def modNorm (C : TestClass R) : (R ⊗[F] E)ˣ →* ℝ≥0 := C.modu.comp (Units.map (Algebra.norm R : R ⊗[F] E →* R))

variable {σ} {hQ : Q = StdUnn.blk4 0 1 (-1) 0} {C : TestClass R} {ψ : AddChar R ℂ} {JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)}
  {χ : (R ⊗[F] E)ˣ →* Circle} {κ : Type} [Fintype κ] {d : LocDbx σ JA Q κ}
  {om : UG (conjR R σ) (JR R Q) →* Module.End ℂ ((κ → R) → ℂ)} {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} {K : Subgroup (HA R σ Q)}
  {f : HA R σ Q → ℂ}

omit [Invertible (2 : R)] in

theorem mem_secOf : f ∈ secOf σ hQ C om l K ↔ ∃ φ ∈ C.sp κ,
    FiniteDimensional ℂ (Submodule.span ℂ {φ' | ∃ k ∈ K, φ' = om (toUG R σ hQ k) φ}) ∧
      f = fun g => l (om (toUG R σ hQ g) φ) :=
  ⟨fun ⟨φ, h, e⟩ => ⟨φ, h.1, h.2, e.symm⟩, fun ⟨φ, h, h', e⟩ => ⟨φ, ⟨h, h'⟩, e.symm⟩⟩

theorem secOf_le_secLoc (h : IsLocModel σ C ψ JA χ d om) (hl : IsYAdm σ C ψ d l) :
    secOf σ hQ C om l K ≤ secLoc σ hQ C ψ JA χ K := fun _ hf => Submodule.subset_span ⟨κ, _, d, om, l, h, hl, hf⟩

omit [Invertible (2 : R)] in

theorem isKFinite_of_mem_secOf (h : f ∈ secOf σ hQ C om l K) : IsKFinite K f := by
  obtain ⟨φ, hφ, rfl⟩ := h
  obtain ⟨W, _, hW⟩ := (kFin_iff _ K _).1 hφ.2
  exact isKFinite_iff.2 ⟨W.map (coefMap _ l), inferInstance, fun k hk => ⟨_, hW k hk, coefMap_om l φ k⟩⟩

theorem IsLocModel.apply_upP (h : IsLocModel σ C ψ JA χ d om) (hl : IsYAdm σ C ψ d l) (p : upperParabolic R σ Q)
    {φ : (κ → R) → ℂ} (hφ : φ ∈ C.sp κ) : l (om (toUG R σ hQ p) φ) =
      χ (aUp R σ Q p) * npow (modNorm F E C (aUp R σ Q p)) ((m : ℂ) / 2) * l φ := by
  rw [h.2 l hl.1 hl.2 (toUG R σ hQ p) (leviUp R σ Q p) (matR_mul_colY p) φ hφ, Complex.ofReal_cpow (NNReal.coe_nonneg _),
    Fintype.card_fin]
  push_cast
  rfl

theorem law_of_mem_secOf (h : IsLocModel σ C ψ JA χ d om) (hl : IsYAdm σ C ψ d l) (hf : f ∈ secOf σ hQ C om l K)
    (p : upperParabolic R σ Q) (g : HA R σ Q) :
    f (p * g) = χ (aUp R σ Q p) * npow (modNorm F E C (aUp R σ Q p)) ((m : ℂ) / 2) * f g := by
  obtain ⟨φ, hφ, -, rfl⟩ := mem_secOf.1 hf
  simp only [map_mul, Module.End.mul_apply]
  exact h.apply_upP hl p (h.1.pres _ _ hφ)

theorem isKFinite_of_mem_secLoc (hf : f ∈ secLoc σ hQ C ψ JA χ K) : IsKFinite K f := by
  induction hf using Submodule.span_induction with
  | mem f h => obtain ⟨_, _, _, _, _, -, -, h⟩ := h; exact isKFinite_of_mem_secOf h
  | zero => exact .of_invariant fun _ _ _ => rfl
  | add _ _ _ _ h h' => exact h.add h'
  | smul c f _ h =>
    have := h.mul_invariant (f := fun _ => c) fun _ _ _ => rfl
    simp only [mul_comm _ c] at this
    exact this

theorem law_of_mem_secLoc (hf : f ∈ secLoc σ hQ C ψ JA χ K) (p : upperParabolic R σ Q) (g : HA R σ Q) :
    f (p * g) = χ (aUp R σ Q p) * npow (modNorm F E C (aUp R σ Q p)) ((m : ℂ) / 2) * f g := by
  induction hf using Submodule.span_induction with
  | mem f h => obtain ⟨_, _, _, _, _, h1, h2, h⟩ := h; exact law_of_mem_secOf h1 h2 h p g
  | zero => simp
  | add _ _ _ _ h h' => simp only [Pi.add_apply, h, h', mul_add]
  | smul c f _ h => simp only [Pi.smul_apply, h, smul_eq_mul]; ring

theorem indLaw_of_mem_secLoc (hf : f ∈ secLoc σ hQ C ψ JA χ K) :
    IndLaw ((modNorm F E C).comp (aUp R σ Q)) (χ.comp (aUp R σ Q)) (((m : ℂ) - n) / 2 + (n : ℂ) / 2) f := fun p g => by
  rw [show ((m : ℂ) - n) / 2 + (n : ℂ) / 2 = (m : ℂ) / 2 by ring]
  exact law_of_mem_secLoc hf p g

theorem mem_psUp_of_continuous [TopologicalSpace R] (hf : f ∈ secLoc σ hQ C ψ JA χ K) (hc : Continuous f) :
    f ∈ psUp R σ Q (modNorm F E C) K χ (((m : ℂ) - n) / 2) :=
  ⟨indLaw_of_mem_secLoc hf, hc, isKFinite_of_mem_secLoc hf⟩

end Model

section Signs

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n m : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = StdUnn.blk4 0 1 (-1) 0)

theorem hTens_eq_trace {R A α β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype α] [Fintype β]
    (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = Matrix.trace (JAᵀ * (x * JB * (y.map c)ᵀ)) := by
  unfold hTens
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum,
    Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Signs

def _root_.GlobalTheory.WeilM.TestClass.comap {R R' : Type} [CommRing R] [CommRing R'] (C : TestClass R') (e : R ≃+* R') :
    TestClass R where
  sp κ _ := (C.sp κ).comap (LinearMap.funLeft ℂ ℂ fun (y : κ → R') i => e.symm (y i))
  adm κ _ := {l | l ∘ₗ (LinearMap.funLeft ℂ ℂ fun (x : κ → R) i => e (x i)) ∈ C.adm κ}
  modu := C.modu.comp (Units.map (e : R →* R'))

section Comap

variable {R R' : Type} [CommRing R] [CommRing R'] {C : TestClass R'} {e : R ≃+* R'} {κ : Type} [Fintype κ]

end Comap

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

def archClass (w : InfinitePlace F) (hw : w.IsReal) : TestClass w.Completion :=
  realClass.comap (InfinitePlace.Completion.ringEquivRealOfIsReal hw)

def psiAtInf (ψ : AddChar (AF F) ℂ) (w : InfinitePlace F) : AddChar w.Completion ℂ :=
  ψ.compAddMonoidHom (inInf w).toAddMonoidHom

variable (F) in

@[reducible] def invTwo (R : Type) [CommRing R] [Algebra F R] : Invertible (2 : R) :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  Invertible.copy (Invertible.map (algebraMap F R) 2) 2 (map_ofNat _ 2).symm

def secFin (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (χ : (AF F ⊗[F] E)ˣ →* Circle)
    (JA : Matrix (Fin m) (Fin m) E) (v : HeightOneSpectrum (𝓞 F)) : Submodule ℂ (GLoc σ Q v → ℂ) :=
  letI := invTwo F (Fv F v)
  secLoc σ hQ (sbClass (Fv F v)) (LatVac.psiAt ψ v) (JR (Fv F v) JA) (charAt χ v) (KUpFin σ Q v)

def secArch (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (χ : (AF F ⊗[F] E)ˣ →* Circle)
    (JA : Matrix (Fin m) (Fin m) E) (w : InfinitePlace F) (hw : w.IsReal) : Submodule ℂ (GArch σ Q w → ℂ) :=
  letI := invTwo F w.Completion
  secLoc σ hQ (archClass w hw) (psiAtInf ψ w) (JR w.Completion JA) (charAtInf χ w) (KUpArch σ Q w)

variable {σ} {hQ : Q = StdUnn.blk4 0 1 (-1) 0} {ψ : AddChar (AF F) ℂ} {χ : (AF F ⊗[F] E)ˣ →* Circle}
  {JA : Matrix (Fin m) (Fin m) E}

omit [NumberField E] in

theorem secFin_eq (v : HeightOneSpectrum (𝓞 F)) [i : Invertible (2 : Fv F v)] : secFin σ hQ ψ χ JA v =
    secLoc σ hQ (sbClass (Fv F v)) (LatVac.psiAt ψ v) (JR (Fv F v) JA) (charAt χ v) (KUpFin σ Q v) := by
  rw [Subsingleton.elim i (invTwo F _)]; rfl

theorem modNorm_sbClass (v : HeightOneSpectrum (𝓞 F)) : modNorm F E (sbClass (Fv F v)) = absEv F E v :=
  MonoidHom.ext fun x => by
    have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _
      (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) x).ne_zero
    rw [Units.mk0_val] at this
    exact this

theorem archClass_modu (w : InfinitePlace F) (hw : w.IsReal) (a : w.Completionˣ) : (archClass w hw).modu a = ‖a.1‖₊ :=
  NNReal.eq ((SiegelModel.real_modu _).trans
    ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a.1))

theorem modNorm_archClass (w : InfinitePlace F) (hw : w.IsReal) : modNorm F E (archClass w hw) = absEw F E w :=
  MonoidHom.ext fun x => by
    rw [absEw_apply, InfinitePlace.mult, if_pos hw, pow_one]
    exact archClass_modu w hw _

theorem law_of_mem_secFin {v : HeightOneSpectrum (𝓞 F)} {f : GLoc σ Q v → ℂ} (hf : f ∈ secFin σ hQ ψ χ JA v)
    (p : upperParabolic (Fv F v) σ Q) (g : GLoc σ Q v) :
    f (p * g) = charAt χ v (aUp _ σ Q p) * npow (absEv F E v (aUp _ σ Q p)) ((m : ℂ) / 2) * f g :=
  letI := invTwo F (Fv F v)
  modNorm_sbClass (E := E) v ▸ law_of_mem_secLoc hf p g

theorem law_of_mem_secArch {w : InfinitePlace F} {hw : w.IsReal} {f : GArch σ Q w → ℂ} (hf : f ∈ secArch σ hQ ψ χ JA w hw)
    (p : upperParabolic w.Completion σ Q) (g : GArch σ Q w) :
    f (p * g) = charAtInf χ w (aUp _ σ Q p) * npow (absEw F E w (aUp _ σ Q p)) ((m : ℂ) / 2) * f g :=
  letI := invTwo F w.Completion
  modNorm_archClass (E := E) w hw ▸ law_of_mem_secLoc hf p g

theorem mem_psUp_fin {v : HeightOneSpectrum (𝓞 F)} {f : GLoc σ Q v → ℂ} (hf : f ∈ secFin σ hQ ψ χ JA v)
    (hc : Continuous f) : f ∈ psUp _ σ Q (absEv F E v) (KUpFin σ Q v) (charAt χ v) (((m : ℂ) - n) / 2) :=
  letI := invTwo F (Fv F v)
  modNorm_sbClass (E := E) v ▸ mem_psUp_of_continuous hf hc

end Places

example : (columnBlock ℤ 1 : Matrix (Fin 2) (Fin 1) ℤ) = !![1; 0] := by decide

example {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (κ : Type) [Fintype κ] :
    (LinearMap.proj 0 : ((κ → w.Completion) → ℂ) →ₗ[ℂ] ℂ) ∈ (archClass w hw).adm κ :=
  ⟨(BoundedContinuousFunction.evalCLM ℂ 0).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => congrArg f (funext fun _ => map_zero _)⟩

end GlobalTheory.LocSW

end
