import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DensDefs

noncomputable section

namespace Formalism.L2.S.S7.WittLeviSubgroups

open NumberField Module Matrix
open scoped TensorProduct ComplexOrder
open Formalism.MainNotions.S Formalism.L2.S.S7.DensDefs

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} (b : ι → (Fin n → R)) (lev : ι → ℕ)

def stepLo (k : ℕ) : Submodule R (Fin n → R) := Submodule.span R (b '' {r | lev r < k})

def stepHi (k : ℕ) : Submodule R (Fin n → R) := Submodule.span R (b '' {r | k ≤ lev r})

def parGL : Subgroup (GL (Fin n) R) := ⨅ k : ℕ, Formalism.UG.stabGL (stepLo b lev k)

def leviGL : Subgroup (GL (Fin n) R) := parGL b lev ⊓ ⨅ k : ℕ, Formalism.UG.stabGL (stepHi b lev k)

theorem mem_parGL {g : GL (Fin n) R} : g ∈ parGL b lev ↔
    ∀ (k : ℕ) (u : Fin n → R), u ∈ stepLo b lev k ↔ (g : Matrix (Fin n) (Fin n) R) *ᵥ u ∈ stepLo b lev k := by
  unfold parGL
  rw [Subgroup.mem_iInf]
  rfl

def uniGL : Subgroup (GL (Fin n) R) where
  carrier := {g | g ∈ parGL b lev ∧ ∀ (k : ℕ) (u : Fin n → R), u ∈ stepLo b lev (k + 1) →
    (g : Matrix (Fin n) (Fin n) R) *ᵥ u - u ∈ stepLo b lev k}
  one_mem' := ⟨(parGL b lev).one_mem, fun k u _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨(parGL b lev).mul_mem hg hh, fun k u hu => ?_⟩
    have e : ((g * h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u - u =
        (g : Matrix (Fin n) (Fin n) R) *ᵥ ((h : Matrix (Fin n) (Fin n) R) *ᵥ u - u) +
          ((g : Matrix (Fin n) (Fin n) R) *ᵥ u - u) := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (((mem_parGL b lev).1 hg k _).1 (hh' k u hu)) (hg' k u hu)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    have hgi : g⁻¹ ∈ parGL b lev := (parGL b lev).inv_mem hg
    refine ⟨hgi, fun k u hu => ?_⟩
    have hw : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u ∈ stepLo b lev (k + 1) :=
      ((mem_parGL b lev).1 hgi (k + 1) u).1 hu
    have hgw : (g : Matrix (Fin n) (Fin n) R) *ᵥ (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have h1 := hg' k _ hw
    rw [hgw] at h1
    have e : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u - u =
        -(u - ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) := by abel
    rw [e]
    exact Submodule.neg_mem _ h1

end Gen

abbrev WIdx (J n₀ : ℕ) : Type := Fin J ⊕ (Fin n₀ ⊕ Fin J)

def widx0 (J n₀ : ℕ) : WIdx J n₀ ≃ Fin (J + (n₀ + J)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def wittJ {R : Type} [Zero R] [One R] {J n₀ : ℕ} (J0 : Matrix (Fin n₀) (Fin n₀) R) :
    Matrix (WIdx J n₀) (WIdx J n₀) R :=
  Matrix.fromBlocks 0 (Matrix.fromCols 0 1) (Matrix.fromRows 0 1) (Matrix.fromBlocks J0 0 0 0)

def levW {J n₀ : ℕ} (c : Composition J) : WIdx J n₀ → ℕ
  | Sum.inl s => (c.index s : ℕ)
  | Sum.inr (Sum.inl _) => c.length
  | Sum.inr (Sum.inr s) => 2 * c.length - (c.index s : ℕ)

variable (I : AutInst)

abbrev nz (J : ℕ) : ℕ := I.n - 2 * J

def widx {J : ℕ} (hJ : 2 * J ≤ I.n) : WIdx J (nz I J) ≃ Fin I.n :=
  (widx0 J (nz I J)).trans (finCongr (by unfold nz; omega))

structure WittFrame (J : ℕ) where
  hJ : 2 * J ≤ I.n
  B : GL (Fin I.n) I.E
  J0 : Matrix (Fin (nz I J)) (Fin (nz I J)) I.E
  gram : ∀ r s, (Formalism.UG.cT (starRingEnd I.E) (B : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
    (B : Matrix (Fin I.n) (Fin I.n) I.E)) (widx I hJ r) (widx I hJ s) = wittJ J0 r s

def projF : I.GA →* GL (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype.comp (MonoidHom.snd I.Ginf I.Gf)

def projV (v : InfinitePlace I.F) : I.GA →* GL (Fin I.n) ℂ :=
  (Formalism.REAL.UJ (I.ε v)).subtype.comp
    ((Pi.evalMonoidHom (fun w => Formalism.REAL.UJ (I.ε w)) v).comp (MonoidHom.fst I.Ginf I.Gf))

def unitGL (n : ℕ) : Subgroup (GL (Fin n) ℂ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.conjTranspose_mul] at *
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose, hg, Matrix.one_mul, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    have hr : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
      calc ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
          = ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ)) *
              ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg, Matrix.one_mul]
        _ = (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by rw [Matrix.mul_assoc, hr, Matrix.mul_one]
    rw [h1, Matrix.conjTranspose_conjTranspose, ← h1, hr]

def kMax : Subgroup I.GA :=
  (⨅ v, (unitGL I.n).comap (projV I v)) ⊓ (Formalism.UG.stabGL I.Lf).comap (projF I)

namespace WittFrame

variable {I} {J : ℕ} (Fr : WittFrame I J)

def col (r : WIdx J (nz I J)) : Fin I.n → I.E := fun i => (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E) i (widx I Fr.hJ r)

def colF (r : WIdx J (nz I J)) : Fin I.n → I.E ⊗[I.F] Af I.F := inclV I (Fr.col r)

def frV (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  (I.P v)⁻¹ * (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)

def colV (v : InfinitePlace I.F) (r : WIdx J (nz I J)) : Fin I.n → ℂ := fun i => Fr.frV v i (widx I Fr.hJ r)

def flag (c : Composition J) (i : Fin c.length) : Submodule I.E (Fin I.n → I.E) :=
  stepLo Fr.col (levW c) ((i : ℕ) + 1)

def parA (c : Composition J) : Subgroup I.GA :=
  (parGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (parGL (Fr.colV v) (levW c)).comap (projV I v)

def leviA (c : Composition J) : Subgroup I.GA :=
  (leviGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (leviGL (Fr.colV v) (levW c)).comap (projV I v)

def uniA (c : Composition J) : Subgroup I.GA :=
  (uniGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (uniGL (Fr.colV v) (levW c)).comap (projV I v)

def wcF (x : I.GA) : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) (I.E ⊗[I.F] Af I.F) := fun r s =>
  ((((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x.2 *
    (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))) (widx I Fr.hJ r) (widx I Fr.hJ s)

def wcV (x : I.GA) (v : InfinitePlace I.F) : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) ℂ := fun r s =>
  ((Fr.frV v)⁻¹ * uMat (x.1 v) * Fr.frV v) (widx I Fr.hJ r) (widx I Fr.hJ s)

def blkF (c : Composition J) (x : I.GA) (i : Fin c.length) :
    Matrix (Fin (c.blocksFun i)) (Fin (c.blocksFun i)) (I.E ⊗[I.F] Af I.F) := fun p q =>
  Fr.wcF x (Sum.inl (c.embedding i p)) (Sum.inl (c.embedding i q))

def blkV (c : Composition J) (x : I.GA) (v : InfinitePlace I.F) (i : Fin c.length) :
    Matrix (Fin (c.blocksFun i)) (Fin (c.blocksFun i)) ℂ := fun p q =>
  Fr.wcV x v (Sum.inl (c.embedding i p)) (Sum.inl (c.embedding i q))

def leadingBlockFiniteAdelic (x : I.GA) : Matrix (Fin (nz I J)) (Fin (nz I J)) (I.E ⊗[I.F] Af I.F) := fun p q =>
  Fr.wcF x (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inl q))

def leadingBlockAtInfinitePlace (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin (nz I J)) (Fin (nz I J)) ℂ := fun p q =>
  Fr.wcV x v (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inl q))

def lam0 (L0 : Submodule (𝓞 I.E) (Fin (nz I J) → I.E)) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) (Set.range (fun s => Fr.col (Sum.inl s)) ∪ Set.range (fun s => Fr.col (Sum.inr (Sum.inr s))) ∪
    (fun u : Fin (nz I J) → I.E => ∑ p, u p • Fr.col (Sum.inr (Sum.inl p))) '' (L0 : Set (Fin (nz I J) → I.E)))

end WittFrame

structure BaseDatum (J : ℕ) extends WittFrame I J where
  L0 : Submodule (𝓞 I.E) (Fin (nz I J) → I.E)
  base_lattice_dual : ∀ u : Fin (nz I J) → I.E, u ∈ L0 ↔
    ∀ w ∈ L0, Formalism.UG.hform (starRingEnd I.E) J0 w u ∈ (algebraMap (𝓞 I.E) I.E).range
  y : I.GA
  hyF : ∀ w, w ∈ I.Lf ↔ I.fmat y.2 *ᵥ w ∈ lamAf (F := I.F) (toWittFrame.lam0 L0)
  H0 : InfinitePlace I.F → Matrix (Fin (nz I J)) (Fin (nz I J)) ℂ
  base_form_posDef : ∀ v, (H0 v).PosDef
  hyV : ∀ v r s, (((uMat (y.1 v))⁻¹ * toWittFrame.frV v).conjTranspose * ((uMat (y.1 v))⁻¹ * toWittFrame.frV v))
    (widx I hJ r) (widx I hJ s) = Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (H0 v) 0 0 1) r s

def BaseDatum.kZero {J : ℕ} (D : BaseDatum I J) : Subgroup I.GA :=
  (kMax I).map (MulAut.conj D.y).toMonoidHom

end Formalism.L2.S.S7.WittLeviSubgroups

end
