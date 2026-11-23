import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

abbrev UPos (n r : ℕ) : Type := {p : Fin n × Fin n // (p.1 : ℕ) < r ∧ r ≤ (p.2 : ℕ)}

section Ring

variable {n r : ℕ} {R : Type*} [CommRing R]

def blockEntry (X : UPos n r → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0

theorem blockEntry_apply (X : UPos n r → R) (i j : Fin n) :
    blockEntry X i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0 := rfl

theorem blockEntry_mul_blockEntry (X Y : UPos n r → R) : blockEntry X * blockEntry Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [blockEntry_apply, blockEntry_apply]
  split_ifs with h1 h2
  · omega
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

theorem blockEntry_add (X Y : UPos n r → R) : blockEntry (X + Y) = blockEntry X + blockEntry Y := by
  ext i j
  simp only [blockEntry_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem blockEntry_zero : blockEntry (0 : UPos n r → R) = 0 := by
  ext i j
  simp only [blockEntry_apply, Matrix.zero_apply, Pi.zero_apply]
  split_ifs <;> rfl

def unipMatrix (X : UPos n r → R) : Matrix (Fin n) (Fin n) R := 1 + blockEntry X

theorem unipMatrix_mul (X Y : UPos n r → R) : unipMatrix X * unipMatrix Y = unipMatrix (X + Y) := by
  simp only [unipMatrix, mul_add, add_mul, one_mul, mul_one, blockEntry_mul_blockEntry, add_zero,
    blockEntry_add]
  abel

theorem unipMatrix_zero : unipMatrix (0 : UPos n r → R) = 1 := by
  simp [unipMatrix, blockEntry_zero]

def unipGL (X : UPos n r → R) : GL (Fin n) R :=
  ⟨unipMatrix X, unipMatrix (-X), by rw [unipMatrix_mul, add_neg_cancel, unipMatrix_zero],
    by rw [unipMatrix_mul, neg_add_cancel, unipMatrix_zero]⟩

@[simp] theorem coe_unipGL (X : UPos n r → R) :
    ((unipGL X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = unipMatrix X := rfl

theorem coe_unipGL_inv (X : UPos n r → R) :
    (((unipGL X)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = unipMatrix (-X) := rfl

theorem unipGL_add (X Y : UPos n r → R) : unipGL (X + Y) = unipGL X * unipGL Y :=
  Units.ext (unipMatrix_mul X Y).symm

theorem unipGL_zero : unipGL (0 : UPos n r → R) = 1 := Units.ext unipMatrix_zero

theorem unipGL_injective : Function.Injective (unipGL : (UPos n r → R) → GL (Fin n) R) := by
  intro X Y h
  funext p
  have := congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) h
  simp only [coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2] at this
  simpa using this

end Ring

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ}

theorem diagonal_unipGL (ξ : UPos n r → K) :
    AdelicGLn.diagonal K n (unipGL ξ) = unipGL (fun p => algebraMap K 𝔸[K] (ξ p)) := by
  ext i j
  simp only [AdelicGLn.diagonal_apply, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem continuous_unipMatrix :
    Continuous (unipMatrix : (UPos n r → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
  refine continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unipGL :
    Continuous (unipGL : (UPos n r → 𝔸[K]) → AdelicGLn.AdelicGL K n) :=
  Units.continuous_iff.2 ⟨continuous_unipMatrix, continuous_unipMatrix.comp continuous_neg⟩

variable (K n r)

abbrev unipMeasure : Measure (UPos n r → 𝔸[K]) := Measure.pi fun _ => GroundTheory.Global.adeleMeasure K

def unipFundamentalDomain : Set (UPos n r → 𝔸[K]) :=
  Set.univ.pi fun _ => GroundTheory.Global.fundamentalSet K

def unipLattice : AddSubgroup (UPos n r → 𝔸[K]) :=
  (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n r)).range

variable {K n r}

instance countable_unipLattice : Countable (unipLattice K n r) := by
  have := GroundTheory.Global.countable_numberField K
  have e : (unipLattice K n r : Set (UPos n r → 𝔸[K])) =
      Set.range (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n r)) :=
    AddMonoidHom.coe_range _
  have hc : (unipLattice K n r : Set (UPos n r → 𝔸[K])).Countable := e ▸ Set.countable_range _
  exact hc.to_subtype

theorem measurableSet_unipFundamentalDomain : MeasurableSet (unipFundamentalDomain K n r) :=
  MeasurableSet.univ_pi fun _ => GroundTheory.Global.measurableSet_fundamentalSet K

theorem isAddFundamentalDomain_unipFundamentalDomain :
    IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r)
      (unipMeasure K n r) := by
  classical
  refine IsAddFundamentalDomain.mk' measurableSet_unipFundamentalDomain.nullMeasurableSet
    fun X => ?_
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
  refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, ?_, ?_⟩
  · intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
  · rintro ⟨_, ξ, rfl⟩ h
    refine Subtype.ext (funext fun p => ?_)
    have hp : algebraMap K 𝔸[K] (ξ p) + X p ∈ GroundTheory.Global.fundamentalSet K := h p (mem_univ p)
    have : -ξ p = k p := huniq p (-ξ p) (by
      show X p - algebraMap K 𝔸[K] (-ξ p) ∈ GroundTheory.Global.fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    change algebraMap K 𝔸[K] (ξ p) = algebraMap K 𝔸[K] (-k p)
    rw [← this, neg_neg]

theorem exists_isCompact_superset_unipFundamentalDomain :
    ∃ C, IsCompact C ∧ unipFundamentalDomain K n r ⊆ C := by
  refine ⟨Set.univ.pi fun _ => closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)),
    isCompact_univ_pi fun _ => (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod
      (GroundTheory.Global.isCompact_integralFiniteAdeles K), ?_⟩
  intro X hX p _
  exact ⟨subset_closure (hX p (mem_univ p)).1, (hX p (mem_univ p)).2⟩

variable (r) in

def constantTerm (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g) ∂unipMeasure K n r

theorem IsLeftInvariant.unipGL_vadd {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (g : AdelicGLn.AdelicGL K n) (ξ : unipLattice K n r) (X : UPos n r → 𝔸[K]) :
    φ (unipGL (ξ +ᵥ X) * g) = φ (unipGL X * g) := by
  obtain ⟨_, ξ, rfl⟩ := ξ
  change φ (unipGL ((fun p => algebraMap K 𝔸[K] (ξ p)) + X) * g) = _
  rw [unipGL_add, ← diagonal_unipGL, mul_assoc, hφ]

theorem constantTerm_eq_setIntegral {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    {D : Set (UPos n r → 𝔸[K])}
    (hD : IsAddFundamentalDomain (unipLattice K n r) D (unipMeasure K n r))
    (g : AdelicGLn.AdelicGL K n) :
    constantTerm r φ g = ∫ X in D, φ (unipGL X * g) ∂unipMeasure K n r :=
  isAddFundamentalDomain_unipFundamentalDomain.setIntegral_eq hD fun ξ X => hφ.unipGL_vadd g ξ X

theorem integrableOn_constantTerm {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (g : AdelicGLn.AdelicGL K n) :
    IntegrableOn (fun X => φ (unipGL X * g)) (unipFundamentalDomain K n r) (unipMeasure K n r) := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hc : Continuous fun X : UPos n r → 𝔸[K] => φ (unipGL X * g) :=
    hφ.comp (continuous_unipGL.mul continuous_const)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hDC

theorem constantTerm_add {φ ψ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (φ + ψ) g = constantTerm r φ g + constantTerm r ψ g :=
  integral_add (integrableOn_constantTerm hφ g) (integrableOn_constantTerm hψ g)

theorem constantTerm_smul (c : ℂ) (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (c • φ) g = c • constantTerm r φ g :=
  integral_smul c _

theorem constantTerm_zero (g : AdelicGLn.AdelicGL K n) :
    constantTerm r (0 : AdelicGLn.AdelicGL K n → ℂ) g = 0 := by
  simp [constantTerm]

theorem constantTerm_rightTranslate (φ : AdelicGLn.AdelicGL K n → ℂ) (h g : AdelicGLn.AdelicGL K n) :
    constantTerm r (rightTranslate h φ) g = constantTerm r φ (g * h) := by
  simp only [constantTerm, rightTranslate, mul_assoc]

def IsCuspidal (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → r < n → ∀ g, constantTerm r φ g = 0

variable (K n) in

def cuspForms : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsAutomorphicForm φ ∧ IsCuspidal φ}
  zero_mem' := ⟨isAutomorphicForm_zero, fun r _ _ g => constantTerm_zero g⟩
  add_mem' {φ ψ} hφ hψ := ⟨hφ.1.add hψ.1, fun r hr hrn g => by
    rw [constantTerm_add hφ.1.continuous hψ.1.continuous, hφ.2 r hr hrn g, hψ.2 r hr hrn g,
      add_zero]⟩
  smul_mem' c φ hφ := ⟨hφ.1.smul c, fun r hr hrn g => by
    rw [constantTerm_smul, hφ.2 r hr hrn g, smul_zero]⟩

theorem mem_cuspForms {φ : AdelicGLn.AdelicGL K n → ℂ} :
    φ ∈ cuspForms K n ↔ IsAutomorphicForm φ ∧ IsCuspidal φ :=
  Iff.rfl

theorem cuspForms_le_automorphicForms : cuspForms K n ≤ automorphicForms K n :=
  fun _ hφ => hφ.1

end AutomorphicForm

end

end GroundTheory.Automorphic
