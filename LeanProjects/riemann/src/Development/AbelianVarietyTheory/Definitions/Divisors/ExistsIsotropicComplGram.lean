import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GramOfIsWittBasis

noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def IsWeylElt (T : GL (Fin (n + n)) E) (w : UA σ J₂) : Prop := inBasis σ T w = blk 0 1 (-1) 0

variable {σ}

omit [NumberField E] in

theorem incM_mul_inv {k : ℕ} (T : GL (Fin k) E) : incM F T.1 * incM F (T⁻¹).1 = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in

theorem mat_eq_inBasis (T : GL (Fin (n + n)) E) (g : UA σ J₂) :
    mat g = incM F T.1 * inBasis σ T g * incM F (T⁻¹).1 := by
  rw [inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul, Matrix.mul_assoc, incM_mul_inv,
    Matrix.mul_one]

omit [NumberField E] in

theorem inBasis_mul (T : GL (Fin (n + n)) E) (g h : UA σ J₂) :
    inBasis σ T (g * h) = inBasis σ T g * inBasis σ T h := by
  have e : mat (g * h) = mat g * mat h := rfl
  rw [inBasis, inBasis, inBasis, e]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F T.1), incM_mul_inv, Matrix.one_mul]

section Weyl

variable {T : GL (Fin (n + n)) E} {w w' : UA σ J₂}

omit [NumberField E] in

theorem exists_isWeylElt (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) (hT : IsWittBasis σ J l T) :
    ∃ w ∈ ratU σ J₂, IsWeylElt σ T w := WittModel.exists_weyl hσ hl hJ h₂ hT

omit [NumberField E] in

theorem IsWeylElt.mat_mul (h : IsWeylElt σ T w) : mat w * incM F T.1 = incM F T.1 * blk 0 1 (-1) 0 := by
  rw [← h, inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]

omit [NumberField E] in

theorem IsWeylElt.mat_mul_self (h : IsWeylElt σ T w) : mat (w * w) = -1 := by
  have e : (blk 0 1 (-1) 0 * blk 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = -1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]
    refine congrArg (fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) =>
      X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (a₂ := -Matrix.fromBlocks 1 0 0 1) ?_
    rw [Matrix.fromBlocks_neg]
    simp
  rw [mat_eq_inBasis T, inBasis_mul, h, e, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, incM_mul_inv]

omit [NumberField E] in

theorem IsWeylElt.mulVec_diag (h : IsWeylElt σ T w) {J : Matrix (Fin n) (Fin n) E} {l : E} (hT : IsWittBasis σ J l T)
    {v : Fin (n + n) → AE F E} (hv : v ∈ diagSub (AE F E) finSumFinEquiv) :
    mat w *ᵥ v ∈ antiSub (AE F E) finSumFinEquiv := by
  obtain ⟨Z, -, hZ⟩ := hT
  have hT : incM F T.1 = blk 1 (incM F Z) 1 (-incM F Z) := by
    simp only [hZ, incM, blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]
  have hb : ∀ (a b c d : Matrix (Fin n) (Fin n) (AE F E)) (x y : Fin n → AE F E), blk a b c d *ᵥ pairVec finSumFinEquiv x y =
      pairVec finSumFinEquiv (a *ᵥ x + b *ᵥ y) (c *ᵥ x + d *ᵥ y) := fun a b c d x y => by simp [mulVec_pairVec, blk]
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hv
  have e : pairVec finSumFinEquiv x x = incM F T.1 *ᵥ pairVec finSumFinEquiv x 0 := by simp [hT, hb]
  rw [e, Matrix.mulVec_mulVec, h.mat_mul, ← Matrix.mulVec_mulVec, hT, hb, hb, pairVec_mem_antiSub]
  simp [Matrix.neg_mulVec, Matrix.mulVec_neg]

omit [NumberField E] in

theorem IsWeylElt.not_mem_siegelOf (h : IsWeylElt σ T w) {J : Matrix (Fin n) (Fin n) E} {l : E} (hT : IsWittBasis σ J l T)
    (hn : 1 ≤ n) : w ∉ siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype := fun hw => by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  haveI : Invertible (2 : AE F E) := Invertible.copy (Invertible.map (algebraMap F (AE F E)) 2) 2 (map_ofNat _ 2).symm
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := inferInstanceAs (Nontrivial (AF F ⊗[F] E))
  have hv : pairVec finSumFinEquiv (1 : Fin n → AE F E) 1 ∈ diagSub (AE F E) finSumFinEquiv := (pairVec_mem_diagSub _).2 rfl
  have h0 : mat w *ᵥ pairVec finSumFinEquiv (1 : Fin n → AE F E) 1 = 0 :=
    Submodule.disjoint_def.1 (isCompl_diagSub_antiSub finSumFinEquiv).disjoint _ ((hw _).1 hv) (h.mulVec_diag hT hv)
  have h1 := congrArg (mat w *ᵥ ·) h0
  have e : mat w * mat w = -1 := h.mat_mul_self
  simp only [Matrix.mulVec_mulVec, e, Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.mulVec_zero, neg_eq_zero] at h1
  have h2 := congrFun h1 (finSumFinEquiv (.inl ⟨0, hn⟩))
  rw [pairVec_inl] at h2
  exact one_ne_zero h2

end Weyl

variable (σ) in

def IsNormN (νN : Measure (unipN σ J₂)) : Prop :=
  νN.IsHaarMeasure ∧ ∃ 𝓓 : Set (unipN σ J₂), IsFundamentalDomain (ratN σ J₂) 𝓓 νN ∧ νN 𝓓 = 1

section Int

variable (νN : Measure (unipN σ J₂)) (w : UA σ J₂)

def intM (f : UA σ J₂ → ℂ) (g : UA σ J₂) : ℂ := ∫ x : unipN σ J₂, f (w * x * g) ∂νN

def IntConv (f : UA σ J₂ → ℂ) (g : UA σ J₂) : Prop := Integrable (fun x : unipN σ J₂ => f (w * x * g)) νN

def HasIntCont (f : ℂ → UA σ J₂ → ℂ) : Prop :=
  (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → ∀ g, IntConv νN w (f s) g) ∧ ∀ g, Cont.Continues fun s => intM νN w (f s) g

def coefM (f : ℂ → UA σ J₂ → ℂ) (s₁ : ℂ) (k : ℤ) (g : UA σ J₂) : ℂ := Cont.laurent (fun s => intM νN w (f s) g) s₁ k

def contM (f : ℂ → UA σ J₂ → ℂ) (s : ℂ) (g : UA σ J₂) : ℂ := Cont.cont (fun z => intM νN w (f z) g) s

variable {νN w} {f f' : UA σ J₂ → ℂ} {g : UA σ J₂}

omit [NumberField E] in

theorem IntConv.add (h : IntConv νN w f g) (h' : IntConv νN w f' g) : IntConv νN w (f + f') g := Integrable.add h h'

omit [NumberField E] in

theorem IntConv.smul (h : IntConv νN w f g) (c : ℂ) : IntConv νN w (c • f) g := Integrable.smul c h

omit [NumberField E] in

theorem intM_smul (c : ℂ) (f : UA σ J₂ → ℂ) (g : UA σ J₂) : intM νN w (c • f) g = c * intM νN w f g :=
  integral_const_mul c _

variable {φ : ℂ → UA σ J₂ → ℂ}

end Int

section Eis

variable (K : Subgroup (UA σ J₂))

def eisFlat (φ : UA σ J₂ → ℂ) (t : ℂ) (g : UA σ J₂) (z : ℂ) : ℂ :=
  Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
    (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K φ t z) g

def eisAt (φ : UA σ J₂ → ℂ) (t : ℂ) (g : UA σ J₂) : ℂ := Cont.cont (eisFlat K φ t g) t

variable {K}

end Eis

section Sec

variable {JV : Matrix (Fin m) (Fin m) E} {κ : Type} (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ))
  (K : Subgroup (UA σ J₂))

def secMap : ((κ → AF F) → ℂ) →ₗ[ℂ] (UA σ J₂ → ℂ) where
  toFun Φ g := om (1, g) Φ 0
  map_add' Φ Ψ := funext fun g => by simp
  map_smul' a Φ := funext fun g => by simp

omit [NumberField E] in

@[simp] theorem secMap_apply (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : secMap om Φ g = om (1, g) Φ 0 := rfl

omit [NumberField E] in

theorem kFin_iff (Φ : (κ → AF F) → ℂ) : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ↔
    ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, om (1, k) Φ ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

variable [Fintype κ]

def kFinSch : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Φ ∈ schA F κ ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ})}
  zero_mem' := ⟨zero_mem _, (kFin_iff om K _).2 ⟨⊥, inferInstance, fun k _ => by simp⟩⟩
  add_mem' := fun {Φ Ψ} h h' => ⟨add_mem h.1 h'.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    obtain ⟨W', _, hW'⟩ := (kFin_iff om K _).1 h'.2
    exact (kFin_iff om K _).2 ⟨W ⊔ W', inferInstance, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩⟩
  smul_mem' := fun c Φ h => ⟨Submodule.smul_mem _ c h.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    exact (kFin_iff om K _).2 ⟨W, inferInstance, fun k hk => by rw [map_smul]; exact W.smul_mem c (hW k hk)⟩⟩

def secSpace : Submodule ℂ (UA σ J₂ → ℂ) := (kFinSch om K).map (secMap om)

variable {om K}

omit [NumberField E] in

theorem mem_secSpace {f : UA σ J₂ → ℂ} : f ∈ secSpace om K ↔
    ∃ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ∧
      f = fun g => om (1, g) Φ 0 :=
  ⟨fun ⟨Φ, h, e⟩ => ⟨Φ, h.1, h.2, e.symm⟩, fun ⟨Φ, h, h', e⟩ => ⟨Φ, ⟨h, h'⟩, e.symm⟩⟩

end Sec

section Compl

variable {L : Type} [Field L]

def complGram (l : L) (JV : Matrix (Fin m) (Fin m) L) (t : ℕ) : Matrix (Fin (m + (t + t))) (Fin (m + (t + t))) L :=
  blkMat finSumFinEquiv JV (l⁻¹ • blk (0 : Matrix (Fin t) (Fin t) L) 1 1 0)

end Compl

example : complGram (2 : ℚ) !![3] 1 = !![3, 0, 0; 0, 0, 1 / 2; 0, 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complGram, blkMat, blk, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks]

example : (blk (n := 1) 0 1 (-1) 0 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  decide

example (w g : UA σ J₂) (f : UA σ J₂ → ℂ) (hf : Measurable f) (x : unipN σ J₂)
    (hm : Measurable fun y : unipN σ J₂ => w * y * g) : intM (Measure.dirac x) w f g = f (w * x * g) :=
  integral_dirac' _ _ (hf.comp hm).stronglyMeasurable

end GlobalTheory.SWInt

end
