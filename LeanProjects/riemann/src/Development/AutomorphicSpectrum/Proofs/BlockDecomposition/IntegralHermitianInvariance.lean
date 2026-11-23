import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInv

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen
  PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trPair_add_left (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R (A + B) C = trPair (F := F) (E := E) R A C + trPair (F := F) (E := E) R B C := by
  simp only [trPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

theorem trPair_add_right (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R A (B + C) = trPair (F := F) (E := E) R A B + trPair (F := F) (E := E) R A C := by
  simp only [trPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem multiplicity_add_lattice_preserving {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R))
    (L : AddSubgroup (Fin n → R)) (b h : Matrix (Fin n) (Fin n) R) (hh : ∀ y ∈ L, h.mulVec y ∈ L) :
    nu2 lam L L (b + h) = nu2 lam L L b := by
  have e : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + (b + h).mulVec y'} = {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + b.mulVec y'} := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y + h.mulVec y', L.add_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y - h.mulVec y', L.sub_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
  simp only [nu2, e]

section Good

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem trPair_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {A B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    trPair (F := F) (E := E) (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  have e : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
    rw [one_div, map_inv₀, map_ofNat]
  rw [trPair, e]
  exact mul_mem hG.half_mem (hG.trace_mem
    (sum_mem fun a _ => sum_mem fun c _ => mul_mem (hA a c) (hB c a)))

theorem gramR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV (M := M) (n := n) bs v) (a c : Fin n) : gramR (Fv F v) σ J Y a c ∈ S := by
  have hmem : ∀ a i, Y a i ∈ S := fun a i => by
    have : Y a i ∈ (S : Set (Fv F v ⊗[F] E)) := by
      rw [hG.carrier]
      exact fun k => hY a i k
    exact this
  have hsig : ∀ x ∈ S, sigR (Fv F v) σ x ∈ S := fun x hx => by
    have := (σS ⟨x, hx⟩).2
    rwa [hG.sig ⟨x, hx⟩] at this
  show ∑ i, ∑ j, sigR (Fv F v) σ (Y a i) * JR (Fv F v) J i j * Y c j ∈ S
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hsig _ (hmem a i)) (hG.J_int i j)) (hmem c j)

theorem jtR_add (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (b + h) = jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) b := by
  unfold jtR
  congr 1
  funext Y
  by_cases hY : Y ∈ latV (M := M) (n := n) bs v
  · have h1 : ψv (trPair (F := F) (E := E) (Fv F v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)) = 1 :=
      hG.psi_of_mem (trPair_mem hG hh (gramR_mem hG hY))
    rw [AddSubgroup.coe_add, trPair_add_left, hG.psi_add, h1, mul_one]
  · simp [Set.indicator_of_notMem hY]

theorem character_add_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (hT : ∀ a b, σ (T b a) = T a b)
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (b + h).1) = ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 b.1) := by
  have h1 : trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1 ∈ v.adicCompletionIntegers F :=
    trPair_mem hG (fun i j => hG.T_int i j) hh
  have h2 : ψv (-trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1) = 1 :=
    hG.psi_of_mem (neg_mem h1)
  rw [AddSubgroup.coe_add, trPair_add_right, neg_add, hG.psi_add, h2, mul_one]

theorem mulVec_mem_L (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ i j, h i j ∈ S) (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ L) : h.mulVec y ∈ L := by
  have key : ∀ w : Fin n → Fv F v ⊗[F] E, w ∈ L ↔ ∀ a, w a ∈ S := fun w => by
    have e1 : w ∈ L ↔ w ∈ (latO bs v : Set (Fin n → Fv F v ⊗[F] E)) := by
      rw [← hL]; rfl
    have e2 : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by
      rw [← hG.carrier]; rfl
    rw [e1]
    simp only [e2]
    rfl
  rw [key] at hy ⊢
  intro a
  show ∑ j, h a j * y j ∈ S
  exact sum_mem fun j _ => mul_mem (hh a j) (hy j)

end Good

theorem integrand_invariant_integral_hermitian : HermitianLatticeInvariance := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  unfold whI
  rw [jtR_add hG μv b h hh, character_add_integral_hermitian hG hT b h hh]
  have e : nu2 lam L L (b + h).1 = nu2 lam L L b.1 := by
    rw [AddSubgroup.coe_add]
    exact multiplicity_add_lattice_preserving lam L _ _ (mulVec_mem_L hG L hL _ hh)
  rw [e]

end GlobalTheory.CompanionTheory.GunrInv

end
