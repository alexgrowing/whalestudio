import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GramOfIsWittBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchANe
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU GlobalTheory.SiegelCoefTheta

namespace GlobalTheory.WeilEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Impl

variable {a b : ℕ} {JX : Matrix (Fin a) (Fin a) E} {JW : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]

structure Impl (ψ : AddChar (AF F) ℂ) (co : Darboux (sy σ JX JW) κ) (g : UA σ JX × UA σ JW)
    (S : Module.End ℂ ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) g w) (S φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S ∈ (adeleClass F).adm κ
  unit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

theorem actAB_mul (g g' : UA σ JX × UA σ JW) (w : Matrix (Fin a) (Fin b) (AE F E)) :
    actAB (cA σ) (g * g') w = actAB (cA σ) g (actAB (cA σ) g' w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

variable {ψ : AddChar (AF F) ℂ} {co : Darboux (sy σ JX JW) κ}

theorem Impl.mul {g g' : UA σ JX × UA σ JW} {S S' : Module.End ℂ ((κ → AF F) → ℂ)} (h : Impl ψ co g S)
    (h' : Impl ψ co g' S') : Impl ψ co (g * g') (S * S') :=
  ⟨fun φ hφ => h.pres _ (h'.pres φ hφ),
    fun w φ hφ => by
      rw [Module.End.mul_apply, h'.Heisenberg₂ w φ hφ, h.Heisenberg₂ _ _ (h'.pres φ hφ), actAB_mul, Module.End.mul_apply],
    fun l hl => h'.adm _ (h.adm l hl),
    fun μ hμ φ hφ => by rw [Module.End.mul_apply, h.unit μ hμ _ (h'.pres φ hφ), h'.unit μ hμ φ hφ]⟩

end Impl

variable {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

variable (σ JV J₂) in

def parG : Subgroup (UA σ JV × UA σ J₂) :=
  (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype).comap (MonoidHom.snd _ _)

def toP : parG σ JV J₂ →* siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype :=
  ((MonoidHom.snd (UA σ JV) (UA σ J₂)).comp (parG σ JV J₂).subtype).codRestrict _ fun q => q.2

def detP : parG σ JV J₂ →* (AE F E)ˣ :=
  (aOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype).comp toP

def scal (χ : Chr F E) (q : parG σ JV J₂) : ℂ :=
  (χ (detP q) : ℂ) * Doubling.npow (absE F E (detP q)) ((m : ℂ) / 2)

def parOp (ψ : AddChar (AF F) ℂ) (χ : Chr F E) (co : Darboux (sy σ JV J₂) κ) (q : parG σ JV J₂) :
    Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ x := scal χ q * co.rho ψ (actAB (cA σ) (q.1)⁻¹ (antiPt co x)) Φ 0
  map_add' Φ Φ' := by funext x; simp only [Darboux.rho, schr, Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def weylFun (ψ : AddChar (AF F) ℂ) (co : Darboux (sy σ JV J₂) κ) [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F))
    (w : UA σ J₂) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  ∫ y, Φ y * ψ (y ⬝ᵥ (co.e (antiPt co x * (mat w⁻¹)ᵀ)).2) ∂μ

def chInt (ψ : AddChar (AF F) ℂ) (co : Darboux (sy σ JV J₂) κ) [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F))
    (b : UA σ J₂) (Φ : (κ → AF F) → ℂ) : ℂ :=
  ∫ x, coefChar co ψ x b * Φ x ∂μ

variable (E) in

def diagA (d : Fin n → AF F) : Matrix (Fin n) (Fin n) (AE F E) :=
  Matrix.diagonal fun j => algebraMap (AF F) (AE F E) (d j)

open scoped Classical in
variable (F) in

def nInf : AF F →* ℝ where
  toFun a := ∏ w : {w : InfinitePlace F // w.IsReal}, (evI F a).1 w
  map_one' := by
    rw [show evI F 1 = 1 from map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)]
    simp
  map_mul' a b := by
    rw [show evI F (a * b) = evI F a * evI F b from map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1]
    simp [Finset.prod_mul_distrib]

section Gauss

variable {ι : Type} [Fintype ι]

def gaussB (α : ι → F) (D : F) (x y : ι ⊕ ι → AF F) : AF F :=
  2 * ∑ k, algebraMap F (AF F) (α k) *
    (x (.inl k) * y (.inl k) + algebraMap F (AF F) D * (x (.inr k) * y (.inr k)))

def gaussQ (α : ι → F) (D : F) (δ : ι → AF F) (x : ι ⊕ ι → AF F) : AF F :=
  ∑ k, δ k * algebraMap F (AF F) (α k) * (x (.inl k) ^ 2 + algebraMap F (AF F) D * x (.inr k) ^ 2)

end Gauss

end GlobalTheory.WeilEx

end
