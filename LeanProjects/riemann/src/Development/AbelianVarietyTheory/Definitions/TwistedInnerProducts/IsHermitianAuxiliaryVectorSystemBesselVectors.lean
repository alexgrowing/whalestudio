import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemLevelFunOfIsAutFun

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

section Generic

variable {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra F K] (τ : E →ₐ[F] K)
  {l m : Type} [Fintype l] [Fintype m]

theorem comp_vecMul (x : l → E) (M : Matrix l m E) : τ ∘ (x ᵥ* M) = (τ ∘ x) ᵥ* M.map τ :=
  funext fun j => by simp [vecMul, dotProduct]

theorem comp_mulVec (M : Matrix l m E) (x : m → E) : τ ∘ (M *ᵥ x) = M.map τ *ᵥ (τ ∘ x) :=
  funext fun j => by simp [mulVec, dotProduct]

theorem comp_dotProduct (x y : l → E) : (τ ∘ x) ⬝ᵥ (τ ∘ y) = τ (x ⬝ᵥ y) := by simp [dotProduct]

theorem dot_mem (I : Ideal K) (u x : l → K) {M : Matrix l l K} (h : ∀ i j, M i j ∈ I) : u ⬝ᵥ M *ᵥ x ∈ I :=
  I.sum_mem fun _ _ => I.mul_mem_left _ (I.sum_mem fun _ _ => I.mul_mem_right _ (h _ _))

theorem sandwich_mem (I : Ideal K) (P : Matrix m l K) (Q : Matrix l m K) {M : Matrix l l K} (h : ∀ i j, M i j ∈ I) (i j : m) :
    (P * M * Q) i j ∈ I :=
  I.sum_mem fun _ _ => I.mul_mem_right _ (I.sum_mem fun _ _ => I.mul_mem_left _ (h _ _))

theorem map_dot (φ : E →+* K) (x : l → E) (M : Matrix l m E) (y : m → E) :
    φ (x ⬝ᵥ M *ᵥ y) = (φ ∘ x) ⬝ᵥ M.map φ *ᵥ (φ ∘ y) := by simp [dotProduct, mulVec]

theorem ext_by_one_mul {m' n c : Type} [Fintype m'] [Fintype n] [Fintype c] [DecidableEq m] [DecidableEq m'] [DecidableEq c]
    {J : Matrix m m' K} {P : Matrix m' m K} {G : Matrix m' m' K} {Γ : Matrix m' n K} {g : Matrix n n K} {B : Matrix m c K}
    (h1 : P * J = 1) (h2 : P * B = 0) (h3 : G * Γ = Γ * g) :
    (1 + J * (G - 1) * P) * fromCols (J * Γ) B =
      fromCols (J * Γ) B * (fromBlocks g 0 0 1 : Matrix (n ⊕ c) (n ⊕ c) K) := by
  rw [fromCols_mul_fromBlocks, mul_fromCols, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ P, Matrix.mul_assoc _ P, h2,
    ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.sub_mul, h3]
  simp [Matrix.mul_sub, Matrix.mul_assoc]

theorem map_ext_by_one {m' : Type} [Fintype m'] [DecidableEq m] [DecidableEq m'] (φ : E →+* K)
    (J : Matrix m m' E) (P : Matrix m' m E) (G : Matrix m' m' E) :
    (1 + J * (G - 1) * P).map φ = 1 + J.map φ * (G.map φ - 1) * P.map φ := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem smul_dot_inv [DecidableEq l] (φ : K →+* K) {G G' : Matrix l l K} (h : G' * G = 1) (hG : (G.map φ)ᵀ = G) (b : K)
    (x : l → K) : (b • (x ᵥ* G)) ⬝ᵥ G' *ᵥ (φ ∘ (b • (x ᵥ* G))) = b * (φ b * x ⬝ᵥ G *ᵥ (φ ∘ x)) := by
  have h1 : φ ∘ (b • (x ᵥ* G)) = φ b • G *ᵥ (φ ∘ x) := by
    funext i
    rw [← hG, mulVec_transpose, hG]
    exact (map_mul φ _ _).trans (congrArg _ (RingHom.map_vecMul φ G x i))
  rw [h1, mulVec_smul, mulVec_mulVec, h, one_mulVec, smul_dotProduct, dotProduct_smul, ← dotProduct_mulVec, smul_eq_mul,
    smul_eq_mul]

end Generic

section Coef

variable (D v) in

def locIdeal : Ideal (AE D) where
  carrier := {z | tensAt D.host.E v (compFin D.host.F D.host.E v z) = z}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change tensAt _ v _ = _
    rw [map_add, map_add, ha, hb]
  smul_mem' := fun a z hz => by
    change tensAt _ v (compFin _ _ v (a * z)) = a * z
    rw [map_mul, mul_comm, ← GlobalTheory.EmbChart.tensAt_mul_right, hz, mul_comm]

theorem tensAt_mem (y : Fv D.host.F v ⊗[D.host.F] D.host.E) : tensAt D.host.E v y ∈ locIdeal D v :=
  congrArg _ (GlobalTheory.EmbChart.compFin_tensAt v y)

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem trace_of_mem {z : AE D} (hz : z ∈ locIdeal D v) :
    Algebra.trace (AF D.host.F) (AE D) z = atPlace v (piW τ z + piW τ (cA D z)) := by
  obtain ⟨y, rfl⟩ : ∃ y, tensAt D.host.E v y = z := ⟨_, hz⟩
  refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
  change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
  have h : cA D (tensAt D.host.E v y) = _ := GlobalTheory.EmbChart.sigR_tensAt v D.sp.cm.sig y
  rw [GlobalTheory.FockCompare.SymplVal.trace_AE, h, ← map_add]
  simp only [piW, RingHom.comp_apply, GlobalTheory.EmbChart.compFin_tensAt, RingHom.coe_coe]
  refine congrArg (tensAt D.host.E v) (a₂ := _ ⊗ₜ 1) (GlobalTheory.AdelicU.split_ext (isCMExt_host D) τ ?_ ?_)
  · simp
  · rw [map_add, GlobalTheory.AdelicU.splitProj_comp_sigR (isCMExt_host D), GlobalTheory.AdelicU.splitProj_comp, add_comm]; simp

def hQ (V : HSp D) (x y : Fin V.rank → D.host.E) : D.host.E := star y ⬝ᵥ V.gram *ᵥ x

def hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) : AE D := ratV (star y) ⬝ᵥ (gA V * mt V g) *ᵥ ratV x

variable (V : HSp D)

theorem cA_ratV {m : ℕ} (x : Fin m → D.host.E) : cA D ∘ ratV x = ratV (star x) := rfl

theorem gA_mul_mt_inv (g : GA D V) : gA V * mt V g⁻¹ = adj (mt V g) * gA V := by rw [mt_inv, gA_giA_cancel]

theorem cA_hA (g : GA D V) (x y : Fin V.rank → D.host.E) : cA D (hA V g x y) = hA V g⁻¹ y x := by
  have h : adj (gA V * mt V g) = gA V * mt V g⁻¹ := by rw [gA_mul_mt_inv, adj_mul, adj_gA]
  rw [hA, hA, ← h, adj, dotProduct_mulVec (ratV (star x)), vecMul_transpose, dotProduct_comm _ (ratV y), map_dot,
    cA_ratV, cA_ratV, star_star]

theorem incA_hQ (x y : Fin V.rank → D.host.E) : incA D (hQ V x y) = hA V 1 x y := by
  rw [hA, mt_one, mul_one, gA, ← ratV_mulVec, hQ, RingHom.map_dotProduct]; rfl

theorem star_hQ (x y : Fin V.rank → D.host.E) : star (hQ V x y) = hQ V y x :=
  incA_injective (by rw [incA_hQ, ← inv_one, ← cA_hA, ← incA_hQ]; rfl)

theorem piW_hA (g : GA D V) (x y : Fin V.rank → D.host.E) :
    piW τ (hA V g x y) = (τ ∘ (star y ᵥ* V.gram)) ⬝ᵥ (mt V g).map (piW τ) *ᵥ (τ ∘ x) := by
  have h1 : ratV (star y) ᵥ* gA V = ratV (star y ᵥ* V.gram) := funext fun i => (RingHom.map_vecMul (incA D) _ _ i).symm
  have h2 {m : ℕ} (x : Fin m → D.host.E) : piW τ ∘ ratV x = τ ∘ x := funext fun i => piW_incA τ _
  rw [hA, ← mulVec_mulVec, dotProduct_mulVec, h1, map_dot, h2, h2]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

theorem hA_locGL_mem (g : GL ι (Fv D.host.F v)) {x y : Fin V.rank → D.host.E} (h : hQ V x y = 0) :
    hA V (locGL V τ β g) x y ∈ locIdeal D v := by
  have e : hA V (locGL V τ β g) x y = (ratV (star y) ᵥ* gA V) ⬝ᵥ (mt V (locGL V τ β g) - 1) *ᵥ ratV x := by
    rw [← dotProduct_mulVec, mulVec_mulVec, mul_sub, sub_mulVec, dotProduct_sub, ← mt_one V, ← hA, ← hA, ← incA_hQ, h,
      map_zero, sub_zero]
  rw [e]
  refine dot_mem _ _ _ fun i j => ?_
  rw [mt_locGL_sub_one]
  exact tensAt_mem _

theorem eq_locGL {x : GA D V} (hx : ∀ i j, (mt V x - 1) i j ∈ locIdeal D v) {g : GL ι (Fv D.host.F v)}
    (h : (mt V x).map (piW τ) * cols β = cols β * g.val) : x = locGL V τ β g := by
  have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v x = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (locGL V τ β g) := by
    refine GlobalTheory.AdelicU.splitHom_injective (isCMExt_host D) (hermND V) τ (Units.ext ?_)
    rw [← map_piW, ← map_piW, map_piW_locGL, conj_val, ← h, Matrix.mul_assoc, cols_mul_rows, Matrix.mul_one]
  refine mt_injective V (sub_left_injective (b := 1) (Matrix.ext fun i j => ?_))
  have h2 : (mt V (locGL V τ β g) - 1) i j ∈ locIdeal D v := by rw [mt_locGL_sub_one]; exact tensAt_mem _
  refine (hx i j).symm.trans (Eq.trans (congrArg _ ?_) h2)
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub]
  exact congrArg (fun y => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram y).val i j - _) h1

end Coef

section Frames

open GlobalTheory.RootEx (N embX)

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def ent {k : Type} [Field k] (g : GL (n ⊕ Fin c) k) (i : ℕ) : k :=
  if h : i + 1 < c then g.val (.inr ⟨i, by omega⟩) (.inr ⟨i + 1, h⟩) else 0

theorem simpleSum_eq_sum_ent {k : Type} [Field k] (g : GL (n ⊕ Fin c) k) :
    GlobalTheory.RootEx.simpleSum g = ∑ i ∈ Finset.range (c - 1), ent g i := by
  have h : ∑ i ∈ Finset.range (c - 1), ent g i = ∑ i ∈ Finset.range c, ent g i :=
    Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi =>
      dif_neg (by rw [Finset.mem_range] at hi; omega)
  rw [h, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ent
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i + 1, hi⟩, if_pos rfl]
    · exact fun j _ hj => if_neg fun e => hj (Fin.ext e)
    · exact fun e => absurd (Finset.mem_univ _) e
  · exact Finset.sum_eq_zero fun j _ => if_neg (by omega)

theorem ent_inv {k : Type} [Field k] {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (i : ℕ) :
    ent g⁻¹ i = -ent g i := by
  unfold ent
  split_ifs with hi
  · have h := GlobalTheory.RootEx.Radical.Uni.mul_apply_succ (b := GlobalTheory.RootEx.lev p) ((GlobalTheory.RootEx.Radical.mem_N_iff _).1 (inv_mem hg))
      ((GlobalTheory.RootEx.Radical.mem_N_iff _).1 hg) (r := .inr ⟨i, by omega⟩) (s := .inr ⟨i + 1, hi⟩) rfl
    rw [Units.inv_mul, Matrix.one_apply_ne (by simp)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  · exact neg_zero.symm

variable (V X : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
  (jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E) (a : ℕ → Fin V.rank → D.host.E)
  (γ : LatFrame (Fv D.host.F v) n (Fin X.rank)) (β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank))

def IsScaled (t : ℕ → Fv D.host.F v) : Prop :=
  (∀ r, vec β (.inl r) = jX.map τ *ᵥ vec γ r) ∧ ∀ i : Fin c, vec β (.inr i) = t i • (τ ∘ a i)

def IsAdapted : Prop := ∃ t, IsScaled V X τ jX a γ β t

def IsNormalFrame (U : Subgroup (GL (n ⊕ Fin c) (Fv D.host.F v))) (χ : GA D V → ℂ) (ψv : AddChar (Fv D.host.F v) Circle) :
    Prop :=
  IsAdapted V X τ jX a γ β ∧ ∀ g ∈ U, χ (locGL V τ β g) = (ψv (GlobalTheory.RootEx.simpleSum g) : ℂ)

variable (c) in

structure IsHermitianAuxiliaryVectorSystem (κ : ℕ → D.host.E) : Prop where
  iso : jXᴴ * V.gram * jX = X.gram
  perp : ∀ i < c, star (a i) ᵥ* V.gram ᵥ* jX = 0
  pair : ∀ i < c, ∀ l < c, hQ V (a l) (a (c - 1 - i)) = if l = i then κ i else 0
  ne : ∀ i < c, κ i ≠ 0
  card : X.rank + c = V.rank

variable {V X τ jX a γ β} {κ : ℕ → D.host.E} {t : ℕ → Fv D.host.F v}

theorem IsScaled.ne_zero (h : IsScaled V X τ jX a γ β t) {i : ℕ} (hi : i < c) : t i ≠ 0 := fun e => by
  have h1 := congrFun (congrFun (rows_mul_cols β) (.inr ⟨i, hi⟩)) (.inr ⟨i, hi⟩)
  have h2 := h.2 ⟨i, hi⟩
  rw [e, zero_smul] at h2
  simp [Matrix.mul_apply, cols_apply, h2] at h1

theorem IsHermitianAuxiliaryVectorSystem.row_inl (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {i : ℕ} (hi : i < c) (u : Fin X.rank → Fv D.host.F v) :
    (τ ∘ (star (a i) ᵥ* V.gram)) ⬝ᵥ jX.map τ *ᵥ u = 0 := by
  rw [dotProduct_mulVec, ← comp_vecMul, H.perp i hi, show τ ∘ (0 : Fin X.rank → D.host.E) = 0 from funext fun _ => map_zero τ,
    zero_dotProduct]

theorem IsHermitianAuxiliaryVectorSystem.row_inr (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {i l : ℕ} (hi : i < c) (hl : l < c) :
    (τ ∘ (star (a (c - 1 - i)) ᵥ* V.gram)) ⬝ᵥ (τ ∘ a l) = if l = i then τ (κ i) else 0 := by
  rw [comp_dotProduct, ← dotProduct_mulVec, ← hQ, H.pair i hi l hl]
  split_ifs
  · rfl
  · exact map_zero _

theorem IsHermitianAuxiliaryVectorSystem.piW_hA (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (hβ : IsScaled V X τ jX a γ β t) (g : GL (n ⊕ Fin c) (Fv D.host.F v))
    (i j : Fin c) : piW τ (hA V (locGL V τ β g) (a j) (a (c - 1 - i))) = τ (κ i) * t i / t j * g.val (.inr i) (.inr j) := by
  have h1 := congrArg ((τ ∘ (star (a (c - 1 - i)) ᵥ* V.gram)) ⬝ᵥ ·) (conj_mulVec_vec β g (.inr j))
  simp only [dotProduct_sum, Fintype.sum_sum_type, dotProduct_add, hβ.1, hβ.2, dotProduct_smul, mulVec_smul,
    H.row_inl (show c - 1 - i < c by omega), H.row_inr i.2 (Fin.is_lt _), smul_eq_mul, mul_zero, Finset.sum_const_zero,
    zero_add, Fin.val_inj, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [LocFrame.piW_hA, map_piW_locGL]
  have := hβ.ne_zero j.2
  field_simp
  linear_combination h1

theorem IsHermitianAuxiliaryVectorSystem.proj_mul (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    (X.gram⁻¹ * (jXᴴ * V.gram)).map τ * jX.map τ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_assoc, H.iso, Matrix.nonsing_inv_mul _ (gram_isUnit_det X)]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

theorem IsHermitianAuxiliaryVectorSystem.exists_isScaled (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (γ : LatFrame (Fv D.host.F v) n (Fin X.rank)) {t : ℕ → Fv D.host.F v} (ht : ∀ i < c, t i ≠ 0) :
    ∃ β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank), IsScaled V X τ jX a γ β t := by
  obtain ⟨β, hβ⟩ := exists_frame (k := Fv D.host.F v) (ι := n ⊕ Fin c) (Y := Fin V.rank)
    (by simp [Fintype.card_congr γ.ord, H.card])
    (fromCols (jX.map τ * cols γ) (Matrix.of fun y (i : Fin c) => t i * τ (a i y))) (fun u hu => by
      have e : (Matrix.of fun y (i : Fin c) => t i * τ (a i y)) *ᵥ (u ∘ Sum.inr) =
          ∑ i : Fin c, (u (.inr i) * t i) • (τ ∘ a i) := by
        funext y
        simp only [mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [fromCols_mulVec, e, ← mulVec_mulVec] at hu
      have h2 (i : Fin c) : u (.inr i) = 0 := by
        have h1 := congrArg ((τ ∘ (star (a (c - 1 - i)) ᵥ* V.gram)) ⬝ᵥ ·) hu
        simp only [dotProduct_sum, dotProduct_add, dotProduct_smul, H.row_inl (show c - 1 - i < c by omega),
          H.row_inr i.2 (Fin.is_lt _), smul_eq_mul, zero_add, Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, dotProduct_zero] at h1
        simpa [ht i i.2, H.ne i i.2] using h1
      simp only [h2, zero_mul, zero_smul, Finset.sum_const_zero, add_zero] at hu
      have h4 := congrArg (fun y => what₂ γ *ᵥ ((X.gram⁻¹ * (jXᴴ * V.gram)).map τ *ᵥ y)) hu
      simp only [mulVec_zero] at h4
      rw [mulVec_mulVec _ _ (jX.map τ), H.proj_mul τ, one_mulVec, mulVec_mulVec, rows_mul_cols, one_mulVec] at h4
      funext r
      rcases r with r | r
      · exact congrFun h4 r
      · exact h2 r)
  exact ⟨β, fun r => funext fun y => congrFun (congrFun hβ y) (.inl r), fun i => funext fun y =>
    congrFun (congrFun hβ y) (.inr i)⟩

theorem IsHermitianAuxiliaryVectorSystem.proj_mulVec (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {i : ℕ} (hi : i < c) :
    (X.gram⁻¹ * (jXᴴ * V.gram)) *ᵥ a i = 0 := by
  have h5 := congrArg star (H.perp i hi)
  rw [vecMul_vecMul, star_vecMul, star_star, conjTranspose_mul, gram_conjTranspose, star_zero] at h5
  rw [← mulVec_mulVec, h5, mulVec_zero]

theorem IsScaled.cols_eq (h : IsScaled V X τ jX a γ β t) :
    cols β = fromCols (jX.map τ * cols γ) (Matrix.of fun y (i : Fin c) => t i * τ (a i y)) := by
  funext y r
  rcases r with r | r
  · exact congrFun (h.1 r) y
  · exact congrFun (h.2 r) y

theorem map_piW_rat {l m : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) : (rat M).map (piW τ) = M.map τ := by
  funext i j
  exact piW_incA τ (M i j)

theorem IsHermitianAuxiliaryVectorSystem.eq_locGL_embX (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (hβ : IsAdapted V X τ jX a γ β) (g : GL n (Fv D.host.F v))
    {x : GA D V} (hx : mt V x = 1 + rat jX ⬝ (mt X (locGL X τ γ g) - 1) ⬝ rat (X.gram⁻¹ * (jXᴴ * V.gram))) :
    x = locGL V τ β (embX c g) := by
  obtain ⟨t, h⟩ := hβ
  refine eq_locGL τ V β (fun i j => ?_) ?_
  · rw [hx, add_sub_cancel_left]
    refine sandwich_mem _ _ _ (fun i j => ?_) i j
    rw [mt_locGL_sub_one]
    exact tensAt_mem _
  have h6 : (X.gram⁻¹ * (jXᴴ * V.gram)).map τ * (Matrix.of fun y (i : Fin c) => t i * τ (a i y)) = 0 := by
    funext y i
    have := congrFun (mulVec_smul ((X.gram⁻¹ * (jXᴴ * V.gram)).map τ) (t i) (τ ∘ a i)) y
    rw [← comp_mulVec, H.proj_mulVec i.2, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, map_zero, smul_zero] at this
    exact this
  rw [hx, map_ext_by_one, map_piW_rat, map_piW_rat, map_piW_locGL, h.cols_eq, GlobalTheory.RootEx.Radical.embX_val]
  exact ext_by_one_mul (H.proj_mul τ) h6 (conj_mul_cols γ g)

end Frames

section Global

open GlobalTheory.RootEx (N embX)

def colN {m ρ : ℕ} (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : ℕ) : Fin m → D.host.E :=
  if h : i < ρ then fun y => M y ⟨i, h⟩ else 0

theorem colN_fin {m ρ : ℕ} (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : Fin ρ) : colN M i = fun y => M y i := dif_pos i.2

def coef (p : ℕ) (a : D.host.E) (i : ℕ) : D.host.E := if i + 1 < p then 1 else if i + 1 = p then a else -1

theorem coef_ne_zero {p : ℕ} {a : D.host.E} (ha : a ≠ 0) (i : ℕ) : coef p a i ≠ 0 := by
  unfold coef
  split_ifs
  exacts [one_ne_zero, ha, neg_ne_zero.2 one_ne_zero]

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  (ζ : Fin L.rank → D.host.E)

def besselAuxiliaryVectors (z : Fin V₀.rank → D.host.E) (i : ℕ) : Fin V.rank → D.host.E :=
  if i < ρ then colN d.e i else if i = ρ then d.i₀ *ᵥ z else colN d.e' (2 * ρ - i)

def fourierJacobiVectors (i : ℕ) : Fin V.rank → D.host.E := if i < ρ then colN d.e i else colN d.e' (2 * ρ - 1 - i)

def fjCharT (n : GA D V) : ℂ := psiFlag ψ d n * ψ (-cenT d L (yZero L ρ ζ) n)

def fjCharS (n : GA D V) : ℂ := psiFlag ψ d n * ψ (cenS d L (zEll L ρ ζ) n)

variable (ψv : AddChar (Fv D.host.F v) Circle) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank))

def IsBesFrame (γ : LatFrame (Fv D.host.F v) n (Fin A.rank)) : Prop :=
  c = 2 * ρ + 1 ∧ IsNormalFrame V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β (N _ n c (ρ + 1))
    (psiBes ψ d 1 (vecB o ζ)) ψv

def IsFJFrameT (γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)) : Prop :=
  c = 2 * ρ ∧ IsNormalFrame V V₀ τ d.i₀ (fourierJacobiVectors d) γ β (N _ n c ρ ⊓ N _ n c (ρ + 1)) (fjCharT ψ d ζ) ψv

def IsFJFrameS (γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)) : Prop :=
  c = 2 * ρ ∧ IsNormalFrame V V₀ τ d.i₀ (fourierJacobiVectors d) γ β (N _ n c ρ ⊓ N _ n c (ρ + 1)) (fjCharS ψ d ζ) ψv

theorem hQ_colN {k l : ℕ} (M : Matrix (Fin V.rank) (Fin k) D.host.E) (M' : Matrix (Fin V.rank) (Fin l) D.host.E) {i j : ℕ}
    (hi : i < k) (hj : j < l) : hQ V (colN M i) (colN M' j) = (M'ᴴ * V.gram * M) ⟨j, hj⟩ ⟨i, hi⟩ := by
  rw [colN, colN, dif_pos hi, dif_pos hj, Matrix.mul_assoc]; rfl

theorem hQ_mulVec {k l : ℕ} (M : Matrix (Fin V.rank) (Fin k) D.host.E) (M' : Matrix (Fin V.rank) (Fin l) D.host.E) (x y) :
    hQ V (M *ᵥ x) (M' *ᵥ y) = star y ⬝ᵥ (M'ᴴ * V.gram * M) *ᵥ x := by
  rw [hQ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem colN_eq_mulVec {m k : ℕ} (M : Matrix (Fin m) (Fin k) D.host.E) {i : ℕ} (hi : i < k) :
    colN M i = M *ᵥ Pi.single ⟨i, hi⟩ 1 := by
  rw [colN, dif_pos hi, mulVec_single_one]; rfl

theorem perp_of_gram {k l : ℕ} {M : Matrix (Fin V.rank) (Fin k) D.host.E} {J : Matrix (Fin V.rank) (Fin l) D.host.E}
    (h : Jᴴ * V.gram * M = 0) (x) : star (M *ᵥ x) ᵥ* V.gram ᵥ* J = 0 := by
  have h1 := congrArg conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero] at h1
  rw [star_mulVec, vecMul_vecMul, vecMul_vecMul, h1, vecMul_zero]

theorem hQ_XX {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e i) (colN d.e j) = 0 := by
  rw [hQ_colN _ _ hi hj, d.ee]; rfl

theorem hQ_YY {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e' i) (colN d.e' j) = 0 := by
  rw [hQ_colN _ _ hi hj, d.e'e']; rfl

theorem hQ_XY {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e i) (colN d.e' j) = if i = j then 1 else 0 := by
  rw [hQ_colN _ _ hi hj, d.e'e, Matrix.one_apply]
  simp only [Fin.mk.injEq, eq_comm]

theorem hQ_YX {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e' i) (colN d.e j) = if j = i then 1 else 0 := by
  rw [← star_hQ, hQ_XY d hj hi]
  split_ifs <;> simp

theorem wittDecomposition_hermitian_e_anisotropicPart {i : ℕ} (hi : i < ρ) (z) : hQ V (colN d.e i) (d.i₀ *ᵥ z) = 0 := by
  rw [colN_eq_mulVec _ hi, hQ_mulVec, d.i₀e, zero_mulVec, dotProduct_zero]

theorem wittDecomposition_hermitian_dual_anisotropicPart {i : ℕ} (hi : i < ρ) (z) : hQ V (colN d.e' i) (d.i₀ *ᵥ z) = 0 := by
  rw [colN_eq_mulVec _ hi, hQ_mulVec, d.i₀e', zero_mulVec, dotProduct_zero]

theorem hQ_0X {i : ℕ} (hi : i < ρ) (z) : hQ V (d.i₀ *ᵥ z) (colN d.e i) = 0 := by
  rw [← star_hQ, wittDecomposition_hermitian_e_anisotropicPart d hi, star_zero]

theorem hQ_0Y {i : ℕ} (hi : i < ρ) (z) : hQ V (d.i₀ *ᵥ z) (colN d.e' i) = 0 := by
  rw [← star_hQ, wittDecomposition_hermitian_dual_anisotropicPart d hi, star_zero]

theorem hQ_vecB : hQ V (d.i₀ *ᵥ vecB o ζ) (d.i₀ *ᵥ vecB o ζ) = hQ L ζ ζ := by
  rw [hQ_mulVec, d.iso, ← hQ, vecB, hQ_mulVec, o.isoB, hQ]

variable {ζ} in
theorem isHermitianAuxiliaryVectorSystem_besselVectors (hζ : IsLineVec L ζ) : IsHermitianAuxiliaryVectorSystem (2 * ρ + 1) V A (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ))
    fun i => if i = ρ then hQ L ζ ζ else 1 where
  iso := by
    rw [conjTranspose_mul, Matrix.mul_assoc o.iAᴴ, Matrix.mul_assoc o.iAᴴ, ← Matrix.mul_assoc _ d.i₀, d.iso,
      ← Matrix.mul_assoc, o.isoA]
  perp i hi := by
    unfold besselAuxiliaryVectors
    split_ifs with h1 h2
    · rw [colN_eq_mulVec _ h1, ← vecMul_vecMul, perp_of_gram d.i₀e, zero_vecMul]
    · rw [vecB, mulVec_mulVec]
      refine perp_of_gram ?_ _
      rw [conjTranspose_mul, Matrix.mul_assoc o.iAᴴ, Matrix.mul_assoc o.iAᴴ, ← Matrix.mul_assoc _ d.i₀, d.iso,
        ← Matrix.mul_assoc, o.orth']
    · rw [colN_eq_mulVec _ (show 2 * ρ - i < ρ by omega), ← vecMul_vecMul, perp_of_gram d.i₀e', zero_vecMul]
  pair i hi l hl := by
    unfold besselAuxiliaryVectors
    rcases lt_trichotomy l ρ with h | h | h <;> rcases lt_trichotomy i ρ with h' | h' | h'
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), hQ_XY d h (by omega), if_neg h'.ne]
      exact if_congr (by omega) rfl rfl
    · rw [if_pos h, if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_e_anisotropicPart d h, if_neg (by omega)]
    · rw [if_pos h, if_pos (by omega), hQ_XX d h (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), hQ_0Y d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega), hQ_vecB, if_pos (by omega), if_pos h']
    · rw [if_neg (by omega), if_pos h, if_pos (by omega), hQ_0X d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hQ_YY d (by omega) (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_dual_anisotropicPart d (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hQ_YX d (by omega) (by omega), if_neg h'.ne']
      exact if_congr (by omega) rfl rfl
  ne i _ := by
    split_ifs
    exacts [hζ.2, one_ne_zero]
  card := by have := d.rank_add; have := o.rank_add; have := hζ.1; omega

theorem isSys_fj : IsHermitianAuxiliaryVectorSystem (2 * ρ) V V₀ d.i₀ (fourierJacobiVectors d) fun _ => 1 where
  iso := d.iso
  perp i hi := by
    unfold fourierJacobiVectors
    split_ifs with h1
    · rw [colN_eq_mulVec _ h1, perp_of_gram d.i₀e]
    · rw [colN_eq_mulVec _ (show 2 * ρ - 1 - i < ρ by omega), perp_of_gram d.i₀e']
  pair i hi l hl := by
    unfold fourierJacobiVectors
    rcases lt_or_ge l ρ with h | h <;> rcases lt_or_ge i ρ with h' | h'
    · rw [if_pos h, if_neg (by omega), hQ_XY d h (by omega)]
      exact if_congr (by omega) rfl rfl
    · rw [if_pos h, if_pos (by omega), hQ_XX d h (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), hQ_YY d (by omega) (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos (by omega), hQ_YX d (by omega) (by omega)]
      exact if_congr (by omega) rfl rfl
  ne _ _ := one_ne_zero
  card := d.rank_add

variable {β}

theorem emb_localGL {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} (hc : c = 2 * ρ)
    (h : IsAdapted V V₀ τ d.i₀ (fourierJacobiVectors d) γ β) (g : GL n (Fv D.host.F v)) :
    d.emb0 (locGL V₀ τ γ g) = locGL V τ β (embX c g) := by
  subst hc
  refine (isSys_fj d).eq_locGL_embX h g ?_
  change _ = 1 + d.j0 ⬝ (mt V₀ (locGL V₀ τ γ g) - 1) ⬝ d.p0
  rw [d.unitaryMatrix_wittCoreEmbedding, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← d.sum_eq_one]
  abel

variable {ζ} in

theorem embA_locGL (hζ : IsLineVec L ζ) {γ : LatFrame (Fv D.host.F v) n (Fin A.rank)} (hc : c = 2 * ρ + 1)
    (h : IsAdapted V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β) (g : GL n (Fv D.host.F v)) :
    embA d o (locGL A τ γ g) = locGL V τ β (embX c g) := by
  subst hc
  refine (isHermitianAuxiliaryVectorSystem_besselVectors d o hζ).eq_locGL_embX h g ?_
  have e : A.gram⁻¹ * ((d.i₀ * o.iA)ᴴ * V.gram) = o.qA * d.q0 := by
    rw [OrthDec.qA, HypDec.q0, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det V₀)]
  rw [e, rat_mul, rat_mul]
  change _ = 1 + d.j0 ⬝ o.jA ⬝ (mt A (locGL A τ γ g) - 1) ⬝ (o.pA ⬝ d.p0)
  have e2 : o.jB ⬝ o.pB = 1 - o.jA ⬝ o.pA := eq_sub_of_add_eq' o.sum_eq_one
  rw [embA_apply, d.unitaryMatrix_wittCoreEmbedding, o.mt_emb, mt_one, Matrix.mul_one, e2, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.one_mul]
  abel

end Global

section Table

open GlobalTheory.RootEx (N embX)
open Finset (range)

variable {V X : HSp D} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {γ : LatFrame (Fv D.host.F v) n (Fin X.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank)}
  {κ : ℕ → D.host.E} {t : ℕ → Fv D.host.F v}

theorem IsHermitianAuxiliaryVectorSystem.simple_mem (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (g : GL (n ⊕ Fin c) (Fv D.host.F v)) {i : ℕ} (hi : i + 1 < c) :
    hA V (locGL V τ β g) (a (i + 1)) (a (c - 1 - i)) ∈ locIdeal D v :=
  hA_locGL_mem τ V β g (by rw [H.pair i (by omega) _ hi, if_neg (by omega)])

theorem IsHermitianAuxiliaryVectorSystem.piW_simple (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (hβ : IsScaled V X τ jX a γ β t)
    (g : GL (n ⊕ Fin c) (Fv D.host.F v)) {i : ℕ} (hi : i + 1 < c) :
    piW τ (hA V (locGL V τ β g) (a (i + 1)) (a (c - 1 - i))) = τ (κ i) * t i / t (i + 1) * ent g i := by
  rw [ent, dif_pos hi]
  exact H.piW_hA hβ g ⟨i, by omega⟩ ⟨i + 1, hi⟩

theorem IsHermitianAuxiliaryVectorSystem.piW_cA_simple (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (hβ : IsScaled V X τ jX a γ β t) {p : ℕ}
    {g : GL (n ⊕ Fin c) (Fv D.host.F v)} (hg : g ∈ N _ n c p) {i : ℕ} (hi : i + 1 < c) :
    piW τ (cA D (hA V (locGL V τ β g) (a (i + 1)) (a (c - 1 - i)))) =
      -(τ (κ (c - 2 - i)) * t (c - 2 - i) / t (c - 2 - i + 1) * ent g (c - 2 - i)) := by
  have h := H.piW_simple hβ g⁻¹ (i := c - 2 - i) (by omega)
  rw [show c - 1 - (c - 2 - i) = i + 1 by omega, ent_inv hg, map_inv, mul_neg] at h
  rw [cA_hA, ← h, show c - 2 - i + 1 = c - 1 - i by omega]

theorem IsHermitianAuxiliaryVectorSystem.trace_sum (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) (hβ : IsScaled V X τ jX a γ β t) {p : ℕ}
    {g : GL (n ⊕ Fin c) (Fv D.host.F v)} (hg : g ∈ N _ n c p) {m : ℕ} (hm : m < c ∨ m = 0) :
    Algebra.trace (AF D.host.F) (AE D) (∑ i ∈ range m, hA V (locGL V τ β g) (a (i + 1)) (a (c - 1 - i))) =
      atPlace v (∑ i ∈ range m, τ (κ i) * t i / t (i + 1) * ent g i -
        ∑ i ∈ range m, τ (κ (c - 1 - m + i)) * t (c - 1 - m + i) / t (c - 1 - m + i + 1) * ent g (c - 1 - m + i)) := by
  rw [← Finset.sum_range_reflect (fun i => τ (κ (c - 1 - m + i)) * t (c - 1 - m + i) / t (c - 1 - m + i + 1) *
    ent g (c - 1 - m + i)), ← Finset.sum_sub_distrib, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < c := by have := Finset.mem_range.1 hi; omega
  rw [trace_of_mem τ (H.simple_mem g hi'), H.piW_simple hβ g hi', H.piW_cA_simple hβ hg hi', sub_eq_add_neg,
    show c - 1 - m + (m - 1 - i) = c - 2 - i by have := Finset.mem_range.1 hi; omega]

variable (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  {ζ : Fin L.rank → D.host.E}

theorem blockX_apply (g : GA D V) (i j : Fin ρ) : blockX d g i j = hA V g (colN d.e j) (colN d.e' i) := by
  rw [blockX, d.pX_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), colN_fin, colN_fin]; rfl

theorem coefX_apply (z : Fin V₀.rank → D.host.E) (g : GA D V) (i : Fin ρ) :
    coefX d z g i = hA V g (d.i₀ *ᵥ z) (colN d.e' i) := by
  rw [coefX, d.pX_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← mulVec_mulVec, ← mulVec_mulVec, hA, ratV_mulVec,
    colN_fin]
  rfl

theorem upSum_blockX (g : GA D V) :
    upSum (blockX d g) = ∑ i ∈ range (ρ - 1), hA V g (colN d.e (i + 1)) (colN d.e' i) := by
  have h : ∑ i ∈ range (ρ - 1), hA V g (colN d.e (i + 1)) (colN d.e' i) =
      ∑ i ∈ range ρ, if i + 1 < ρ then hA V g (colN d.e (i + 1)) (colN d.e' i) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.ext fun i => ?_) fun _ _ => rfl
    simp only [Finset.mem_range, Finset.mem_filter]; omega
  rw [h, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i + 1, hi⟩, if_pos rfl, blockX_apply]
    · exact fun j _ hj => if_neg fun e => hj (Fin.ext e)
    · exact fun e => absurd (Finset.mem_univ _) e
  · exact Finset.sum_eq_zero fun j _ => if_neg (by omega)

theorem ell_dot {σ : ℕ} (x : Fin (σ + 1) → AE D) : ell D (σ + 1) ⬝ᵥ x = x (Fin.last σ) := by
  rw [dotProduct, Finset.sum_eq_single (Fin.last σ), show ell D (σ + 1) (Fin.last σ) = 1 from if_pos rfl, one_mul]
  · intro j _ hj
    rw [show ell D (σ + 1) j = 0 from if_neg fun e => hj (Fin.ext (Nat.succ_injective e)), zero_mul]
  · exact fun e => absurd (Finset.mem_univ _) e

theorem simpleSum_eq_sum_hA (z : Fin V₀.rank → D.host.E) (g : GA D V) : GlobalTheory.MixPer.simpleSum d z g =
    ∑ i ∈ range ρ, hA V g (besselAuxiliaryVectors d z (i + 1)) (besselAuxiliaryVectors d z (2 * ρ + 1 - 1 - i)) := by
  rw [GlobalTheory.MixPer.simpleSum, upSum_blockX]
  cases ρ with
  | zero => simp [dotProduct]
  | succ σ =>
    rw [Finset.sum_range_succ, ell_dot, coefX_apply]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [besselAuxiliaryVectors, besselAuxiliaryVectors, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      congr 2; omega
    · rw [besselAuxiliaryVectors, besselAuxiliaryVectors, if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega)]
      congr 2; simp; omega

theorem upSum_eq_sum_hA (g : GA D V) : upSum (blockX d g) =
    ∑ i ∈ range (ρ - 1), hA V g (fourierJacobiVectors d (i + 1)) (fourierJacobiVectors d (2 * ρ - 1 - i)) := by
  rw [upSum_blockX]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [fourierJacobiVectors, fourierJacobiVectors, if_pos (by omega), if_neg (by omega)]
  congr 2; omega

theorem psiBes_locGL (hζ : IsLineVec L ζ) {γ : LatFrame (Fv D.host.F v) n (Fin A.rank)} (hc : c = 2 * ρ + 1)
    (hβ : IsScaled V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β t) {p : ℕ} {g : GL (n ⊕ Fin c) (Fv D.host.F v)}
    (hg : g ∈ N _ n c p) : psiBes ψ d 1 (vecB o ζ) (locGL V τ β g) =
      psiV _ ψ v (∑ i ∈ range (c - 1), τ (coef (ρ + 1) (-hQ L ζ ζ) i) * t i / t (i + 1) * ent g i) := by
  subst hc
  rw [psiBes, map_one, one_mul, simpleSum_eq_sum_hA, psiE, (isHermitianAuxiliaryVectorSystem_besselVectors d o hζ).trace_sum hβ hg (by omega),
    show 2 * ρ + 1 - 1 = ρ + ρ by omega, Finset.sum_range_add, Nat.add_sub_cancel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine congrArg (fun x => ψ (atPlace v x)) (congrArg₂ _ (Finset.sum_congr rfl fun i hi => ?_)
    (Finset.sum_congr rfl fun i hi => ?_))
  · have := Finset.mem_range.1 hi
    rw [coef, if_neg (by omega), if_pos (by omega)]
  · rw [coef, if_neg (show ¬ ρ + i + 1 < ρ + 1 by omega)]
    by_cases h : i = 0
    · rw [if_pos (by omega), if_pos (by omega), map_neg]; ring
    · rw [if_neg (by omega), if_neg (by omega), map_neg]; ring

theorem hO_vecMulVec (S T : HSp D) (u u' : Fin T.rank → AE D) (r r' : Fin S.rank → AE D) :
    hO S T (vecMulVec u r) (vecMulVec u' r') = (cA D ∘ u') ⬝ᵥ gA T *ᵥ u * r ⬝ᵥ giA S *ᵥ (cA D ∘ r') := by
  have h : adj (vecMulVec u' r') = vecMulVec (cA D ∘ r') (cA D ∘ u') := by
    funext i j
    exact (map_mul (cA D) _ _).trans (mul_comm _ _)
  rw [hO_eq_trace, h, mul_vecMulVec, vecMulVec_mul_vecMulVec, mul_vecMulVec, trace_vecMulVec, dotProduct_comm,
    smul_dotProduct, smul_eq_mul]

theorem trHalf_of_mem {b : D.host.E} (hb : star b = b) {H : AE D} (hH : H ∈ locIdeal D v) {x : Fv D.host.F v}
    (h1 : piW τ H = x) (h2 : piW τ (cA D H) = -x) : trHalf D (incA D b * H) = atPlace v (τ (D.host.xi0 * b) * x) := by
  change algebraMap _ (AF D.host.F) (1 / 2) * Algebra.trace _ _ (incA D D.host.xi0 * (incA D b * H)) = _
  have e (y : D.host.E) : cA D (incA D y) = incA D (star y) := rfl
  rw [trace_of_mem τ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hH)), ← Algebra.smul_def, ← map_smul]
  simp only [map_mul, e, hb, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, piW_incA, h1, h2, map_neg, Algebra.smul_def, map_div₀, map_one,
    map_ofNat]
  haveI : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  congr 1
  ring

theorem jY_mulVec_ell {σ : ℕ} (d : HypDec V V₀ (σ + 1)) : d.jY *ᵥ ell D (σ + 1) = ratV (colN d.e' σ) := by
  funext y
  change d.jY y ⬝ᵥ _ = _
  rw [dotProduct_comm, ell_dot, ratV, colN, dif_pos σ.lt_succ_self]; rfl

theorem cA_mulVec {l m : ℕ} (M : Mx D l m) (x : Fin m → AE D) : cA D ∘ (M *ᵥ x) = (cA D ∘ x) ᵥ* adj M := by
  rw [adj, vecMul_transpose]
  exact funext fun i => RingHom.map_mulVec (cA D) M x i

theorem cA_vecMul {l m : ℕ} (M : Mx D l m) (x : Fin l → AE D) : cA D ∘ (x ᵥ* M) = adj M *ᵥ (cA D ∘ x) := by
  rw [adj, mulVec_transpose]
  exact funext fun i => RingHom.map_vecMul (cA D) M x i

theorem incA_hQ' (x y : Fin V.rank → D.host.E) : ratV (star y) ⬝ᵥ gA V *ᵥ ratV x = incA D (hQ V x y) := by
  rw [incA_hQ, hA, mt_one, mul_one]

theorem incAdj_yZero {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E) : d.incAdj L (yZero L (σ + 1) ζ) =
    vecMulVec (ratV (colN d.e' σ)) (incA D D.host.xi0⁻¹ • (ratV (star ζ) ᵥ* gA L)) := by
  have h0 : adj (vecMulVec (ratV ζ) (ell D (σ + 1))) = vecMulVec (ell D (σ + 1)) (ratV (star ζ)) := by
    funext i j
    refine (map_mul (cA D) _ _).trans ((mul_comm _ _).trans (congrArg₂ _ ?_ rfl))
    unfold ell
    split_ifs <;> simp
  rw [d.incAdj_apply, d.incY_apply, yZero, adj_neg, Matrix.neg_mul, map_neg, neg_smul_neg, zEll, h0, vecMulVec_mul,
    ← vecMulVec_smul, mul_vecMulVec, jY_mulVec_ell]

theorem cA_inv_dot (g : GA D V) (u : Fin V.rank → D.host.E) :
    (cA D ∘ (mt V g⁻¹ *ᵥ ratV u)) ⬝ᵥ gA V *ᵥ ratV u = hA V g u u := by
  rw [cA_mulVec, cA_ratV, ← dotProduct_mulVec, mulVec_mulVec, ← gA_mul_mt_inv, inv_inv, hA]

theorem conj_xi_inv : cA D (incA D D.host.xi0⁻¹) = incA D (-D.host.xi0⁻¹) :=
  congrArg (incA D) (show star _ = _ by rw [star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg])

theorem cenT_eq {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E) (g : GA D V) :
    cenT d L (yZero L (σ + 1) ζ) g =
      trHalf D (incA D (-(D.host.xi0⁻¹ * D.host.xi0⁻¹ * hQ L ζ ζ)) * hA V g (colN d.e' σ) (colN d.e' σ)) := by
  have h3 := smul_dot_inv (cA D) (giA_mul_gA L) (adj_gA L) (incA D D.host.xi0⁻¹) (ratV (star ζ))
  rw [cA_ratV, star_star, incA_hQ', conj_xi_inv, ← map_mul (incA D), ← map_mul (incA D), neg_mul, mul_neg, ← mul_assoc] at h3
  rw [cenT, incAdj_yZero, mul_vecMulVec, symplOH_eq, hO_vecMulVec, cA_inv_dot, mul_comm]
  exact congrArg (fun x => trHalf D (x * _)) h3

theorem cenS_eq {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E) (g : GA D V) :
    cenS d L (zEll L (σ + 1) ζ) g = trHalf D (incA D (hQ L ζ ζ) * hA V g⁻¹ (colN d.e' σ) (colN d.e' σ)) := by
  have h0 : ell D (σ + 1) ᵥ* adj d.jY = ratV (star (colN d.e' σ)) := by
    funext y
    change _ ⬝ᵥ _ = _
    rw [ell_dot, colN, dif_pos σ.lt_succ_self]; rfl
  have h : d.extX L (zEll L (σ + 1) ζ) = vecMulVec (ratV ζ) (ratV (star (colN d.e' σ)) ᵥ* gA V) := by
    rw [d.extX_apply, zEll, vecMulVec_mul, d.pX_eq, ← vecMul_vecMul, h0]
  have h1 (u : Fin V.rank → D.host.E) : (ratV (star u) ᵥ* gA V) ⬝ᵥ giA V *ᵥ (cA D ∘ (ratV (star u) ᵥ* gA V ᵥ* mt V g)) =
      hA V g⁻¹ u u := by
    rw [vecMul_vecMul, cA_vecMul, cA_ratV, star_star, adj_mul, adj_gA, ← gA_mul_mt_inv, ← dotProduct_mulVec,
      mulVec_mulVec, gA_mul_giA, one_mulVec, hA]
  rw [cenS, h, vecMulVec_mul, symplOH_eq, hO_vecMulVec, h1, cA_ratV, incA_hQ']

theorem psiFlag_mul_locGL {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)}
    {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)} (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t) {p : ℕ}
    {g : GL (n ⊕ Fin (2 * (σ + 1))) (Fv D.host.F v)} (hg : g ∈ N _ n _ p) (b : D.host.E) :
    psiFlag ψ d (locGL V τ β g) * ψ (atPlace v (τ b * (t σ / t (σ + 1) * ent g σ))) =
      psiV _ ψ v (∑ i ∈ range (2 * (σ + 1) - 1), τ (coef (σ + 1) b i) * t i / t (i + 1) * ent g i) := by
  rw [psiFlag, upSum_eq_sum_hA, psiE, (isSys_fj d).trace_sum hβ hg (by omega), ← AddChar.map_add_eq_mul, ← map_add,
    show 2 * (σ + 1) - 1 = σ + 1 + σ by omega, Finset.sum_range_add, Finset.sum_range_succ, Nat.add_sub_cancel,
    Nat.add_sub_cancel, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_right_comm]
  refine congrArg (fun x => ψ (atPlace v x)) (congrArg₂ _ (congrArg₂ _ (Finset.sum_congr rfl fun i hi => ?_) ?_)
    (Finset.sum_congr rfl fun i hi => ?_))
  · have := Finset.mem_range.1 hi
    rw [coef, if_pos (by omega)]
  · rw [coef, if_neg (by omega), if_pos rfl]; ring
  · rw [coef, if_neg (by omega), if_neg (by omega), map_neg]; ring

theorem central_locGL {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)}
    {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)} (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t) {p : ℕ}
    {g : GL (n ⊕ Fin (2 * (σ + 1))) (Fv D.host.F v)} (hg : g ∈ N _ n _ p) {b : D.host.E} (hb : star b = b) :
    trHalf D (incA D b * hA V (locGL V τ β g) (colN d.e' σ) (colN d.e' σ)) =
      atPlace v (τ (D.host.xi0 * b) * (t σ / t (σ + 1) * ent g σ)) := by
  have e : fourierJacobiVectors d (σ + 1) = colN d.e' σ := by
    rw [fourierJacobiVectors, if_neg (by omega)]; congr 1; omega
  have h0 := (isSys_fj d).simple_mem (τ := τ) (β := β) g (i := σ) (by omega)
  have h1 := (isSys_fj d).piW_simple hβ g (i := σ) (by omega)
  have h2 := (isSys_fj d).piW_cA_simple hβ hg (i := σ) (by omega)
  rw [show 2 * (σ + 1) - 1 - σ = σ + 1 by omega, e] at h0 h1 h2
  rw [show 2 * (σ + 1) - 2 - σ = σ by omega] at h2
  rw [map_one, one_mul] at h1 h2
  exact trHalf_of_mem hb h0 h1 h2

theorem cmHost_imaginaryGenerator_ne_zero : D.host.xi0 ≠ 0 := fun h => by
  have := HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
  rw [h, map_zero, zero_mul] at this
  exact zero_ne_one (incA_injective ((map_zero _).trans (this.trans (map_one _).symm)))

theorem fjCharT_locGL (ζ : Fin L.rank → D.host.E) {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} (hc : c = 2 * ρ)
    (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t) {p : ℕ} {g : GL (n ⊕ Fin c) (Fv D.host.F v)} (hg : g ∈ N _ n c p) :
    fjCharT ψ d ζ (locGL V τ β g) =
      psiV _ ψ v (∑ i ∈ range (c - 1), τ (coef ρ (D.host.xi0⁻¹ * hQ L ζ ζ) i) * t i / t (i + 1) * ent g i) := by
  subst hc
  cases ρ with
  | zero =>
    have h : d.incAdj L (yZero L 0 ζ) = 0 := (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [fjCharT, psiFlag, upSum_blockX, cenT, h, symplOH_zero_left]
    change _ = ψ (atPlace v _)
    simp [psiE_zero]
  | succ σ =>
    rw [fjCharT, cenT_eq, central_locGL d hβ hg, ← map_neg, ← psiFlag_mul_locGL ψ d hβ hg, ← neg_mul, ← map_neg]
    · congr 5
      field_simp [cmHost_imaginaryGenerator_ne_zero (D := D)]
    · rw [star_neg, star_mul', star_mul', star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, star_hQ, inv_neg, neg_mul_neg]

theorem fjCharS_locGL (ζ : Fin L.rank → D.host.E) {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} (hc : c = 2 * ρ)
    (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t) {p : ℕ} {g : GL (n ⊕ Fin c) (Fv D.host.F v)} (hg : g ∈ N _ n c p) :
    fjCharS ψ d ζ (locGL V τ β g) =
      psiV _ ψ v (∑ i ∈ range (c - 1), τ (coef ρ (-(D.host.xi0 * hQ L ζ ζ)) i) * t i / t (i + 1) * ent g i) := by
  subst hc
  cases ρ with
  | zero =>
    have h : d.extX L (zEll L 0 ζ) = 0 := (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [fjCharS, psiFlag, upSum_blockX, cenS, h, symplOH_zero_left]
    change _ = ψ (atPlace v _)
    simp [psiE_zero]
  | succ σ =>
    rw [fjCharS, cenS_eq, ← map_inv, central_locGL d hβ (inv_mem hg) (star_hQ _ _ _), ent_inv hg,
      ← psiFlag_mul_locGL ψ d hβ hg, map_neg, mul_neg, mul_neg, neg_mul]

end Table

section Normal

open GlobalTheory.RootEx (N)
open Finset (range)

def normScale {k : Type} [Field k] (θ : k) (κ : ℕ → k) (t₀ : k) (i : ℕ) : k := t₀ * ∏ l ∈ range i, κ l / θ

theorem normScale_succ {k : Type} [Field k] {θ : k} (hθ : θ ≠ 0) (κ : ℕ → k) (t₀ : k) (i : ℕ) :
    θ * normScale θ κ t₀ (i + 1) = κ i * normScale θ κ t₀ i := by
  rw [normScale, normScale, Finset.prod_range_succ]
  field_simp

theorem normScale_ne_zero {k : Type} [Field k] {θ : k} (hθ : θ ≠ 0) {κ : ℕ → k} (hκ : ∀ i, κ i ≠ 0) {t₀ : k} (h : t₀ ≠ 0)
    (i : ℕ) : normScale θ κ t₀ i ≠ 0 :=
  mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (hκ l) hθ)

theorem eq_normScale {k : Type} [Field k] {θ : k} (hθ : θ ≠ 0) {κ t : ℕ → k} {c : ℕ}
    (h : ∀ i, i + 1 < c → θ * t (i + 1) = κ i * t i) {i : ℕ} (hi : i < c) : t i = normScale θ κ (t 0) i := by
  induction i with
  | zero => simp [normScale]
  | succ i ih => exact mul_left_cancel₀ hθ (by rw [h i hi, normScale_succ hθ, ← ih (by omega)])

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem exists_root {k : Type} [Field k] {i : ℕ} (hi : i + 1 < c) (x : k) :
    ∃ g : GL (n ⊕ Fin c) k, (∀ p, g ∈ N k n c p) ∧ ∀ j, ent g j = if j = i then x else 0 := by
  let T : TransvectionStruct (n ⊕ Fin c) k := ⟨.inr ⟨i, by omega⟩, .inr ⟨i + 1, hi⟩, by simp, x⟩
  refine ⟨⟨T.toMatrix, T.inv.toMatrix, T.mul_inv, T.inv_mul⟩, fun p => Subgroup.subset_closure fun r s h => ?_, fun j => ?_⟩
  · change (1 + single _ _ x : Matrix _ _ k) r s = _
    rw [Matrix.add_apply, single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    simp [GlobalTheory.RootEx.lev, T] at h
  · unfold ent
    split_ifs with h1 h2 h2
    · subst h2
      change (1 + single _ _ x : Matrix _ _ k) _ _ = _
      rw [Matrix.add_apply, single_apply_same, Matrix.one_apply_ne (by simp), zero_add]
    · change (1 + single _ _ x : Matrix _ _ k) _ _ = _
      rw [Matrix.add_apply, single_apply_of_ne, Matrix.one_apply_ne (by simp), zero_add]
      simp only [T, Sum.inr.injEq, Fin.mk.injEq]; omega
    · omega
    · rfl

variable {V X : HSp D} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v}
  {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {γ : LatFrame (Fv D.host.F v) n (Fin X.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank)}
  {κ t : ℕ → Fv D.host.F v} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {θ : Fv D.host.F v}
  {U : Subgroup (GL (n ⊕ Fin c) (Fv D.host.F v))} {χ : GA D V → ℂ}

theorem isNormalFrame_of_scale (hβ : IsScaled V X τ jX a γ β t)
    (hχ : ∀ g ∈ U, χ (locGL V τ β g) = psiV _ ψ v (∑ i ∈ range (c - 1), κ i * t i / t (i + 1) * ent g i))
    (h : ∀ i, i + 1 < c → θ * t (i + 1) = κ i * t i) : IsNormalFrame V X τ jX a γ β U χ (locChar ψ hψ θ) := by
  refine ⟨⟨t, hβ⟩, fun g hg => ?_⟩
  rw [hχ g hg, coe_locChar, simpleSum_eq_sum_ent, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i hi => ?_)
  have hi' : i + 1 < c := by have := Finset.mem_range.1 hi; omega
  rw [← h i hi', mul_div_cancel_right₀ _ (hβ.ne_zero hi')]

theorem scale_of_isNormalFrame (h1 : locChar ψ hψ θ ≠ 1) (hβ : IsScaled V X τ jX a γ β t)
    (hχ : ∀ g ∈ U, χ (locGL V τ β g) = psiV _ ψ v (∑ i ∈ range (c - 1), κ i * t i / t (i + 1) * ent g i))
    (hU : ∀ g, (∀ p, g ∈ N _ n c p) → g ∈ U) (h : IsNormalFrame V X τ jX a γ β U χ (locChar ψ hψ θ)) {i : ℕ}
    (hi : i + 1 < c) : θ * t (i + 1) = κ i * t i := by
  have key (x) : locChar ψ hψ 1 (κ i * t i / t (i + 1) * x) = locChar ψ hψ 1 (θ * x) := by
    obtain ⟨g, hg, e⟩ := exists_root (n := n) hi x
    have h2 := (hχ g (hU g hg)).symm.trans (h.2 g (hU g hg))
    simp only [coe_locChar, simpleSum_eq_sum_ent, e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
      show i < c - 1 by omega, if_true] at h2
    exact Circle.ext (by rw [coe_locChar, coe_locChar, one_mul, one_mul, h2])
  by_contra hne
  have h3 : κ i * t i / t (i + 1) - θ ≠ 0 := fun e =>
    hne (by rw [← sub_eq_zero.1 e, div_mul_cancel₀ _ (hβ.ne_zero hi)])
  refine h1 (AddChar.ext _ _ fun y => ?_)
  have h4 := key (θ * y / (κ i * t i / t (i + 1) - θ))
  rw [← div_eq_one, ← AddChar.map_sub_eq_div, ← sub_mul, mul_div_cancel₀ _ h3] at h4
  exact Circle.ext (by rw [coe_locChar, ← one_mul (θ * y), ← coe_locChar ψ hψ, h4]; rfl)

theorem ne_zero_of_locChar_ne_one (h1 : locChar ψ hψ θ ≠ 1) : θ ≠ 0 := by
  rintro rfl
  exact h1 (AddChar.ext _ _ fun y => Circle.ext (by
    change ψ _ = 1
    rw [zero_mul, map_zero, AddChar.map_zero_eq_one]))

variable {V₀ A L L' : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) {ζ : Fin L.rank → D.host.E}

section Bes

variable {γ : LatFrame (Fv D.host.F v) n (Fin A.rank)}

theorem isBesFrame_of_scale (hζ : IsLineVec L ζ) (hc : c = 2 * ρ + 1)
    (hβ : IsScaled V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β t)
    (h : ∀ i, i + 1 < c → θ * t (i + 1) = τ (coef (ρ + 1) (-hQ L ζ ζ) i) * t i) :
    IsBesFrame ψ d o ζ (locChar ψ hψ θ) τ β γ :=
  ⟨hc, isNormalFrame_of_scale hψ hβ (fun _ hg => psiBes_locGL ψ d o hζ hc hβ hg) h⟩

theorem IsBesFrame.exists_scale (h1 : locChar ψ hψ θ ≠ 1) (hζ : IsLineVec L ζ)
    (h : IsBesFrame ψ d o ζ (locChar ψ hψ θ) τ β γ) : ∃ t₀, IsScaled V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β
      (normScale θ (fun i => τ (coef (ρ + 1) (-hQ L ζ ζ) i)) t₀) := by
  obtain ⟨t, ht⟩ := h.2.1
  refine ⟨t 0, ht.1, fun i => ?_⟩
  rw [ht.2, eq_normScale (ne_zero_of_locChar_ne_one hψ h1) (fun i hi => scale_of_isNormalFrame hψ h1 ht
    (fun _ hg => psiBes_locGL ψ d o hζ h.1 ht hg) (fun _ hg => hg _) h.2 hi) i.2]

theorem exists_isBesFrame (hζ : IsLineVec L ζ) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (hθ : θ ≠ 0)
    (γ : LatFrame (Fv D.host.F v) n (Fin A.rank)) {t₀ : Fv D.host.F v} (h₀ : t₀ ≠ 0) :
    ∃ β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * ρ + 1)) (Fin V.rank), IsBesFrame ψ d o ζ (locChar ψ hψ θ) τ β γ ∧
      IsScaled V A τ (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ)) γ β
        (normScale θ (fun i => τ (coef (ρ + 1) (-hQ L ζ ζ) i)) t₀) := by
  obtain ⟨β, hβ⟩ := (isHermitianAuxiliaryVectorSystem_besselVectors d o hζ).exists_isScaled τ γ fun i _ => normScale_ne_zero hθ
    (fun i => (map_ne_zero τ).2 (coef_ne_zero (p := ρ + 1) (neg_ne_zero.2 hζ.2) i)) h₀ i
  exact ⟨β, isBesFrame_of_scale hψ d o hζ rfl hβ fun i _ => normScale_succ hθ _ _ i, hβ⟩

end Bes

section FJ

variable {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)}

theorem isFJFrameT_of_scale (hc : c = 2 * ρ) (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
    (h : ∀ i, i + 1 < c → θ * t (i + 1) = τ (coef ρ (D.host.xi0⁻¹ * hQ L ζ ζ) i) * t i) :
    IsFJFrameT ψ d ζ (locChar ψ hψ θ) τ β γ :=
  ⟨hc, isNormalFrame_of_scale hψ hβ (fun _ hg => fjCharT_locGL ψ d ζ hc hβ hg.1) h⟩

theorem IsFJFrameT.exists_scale (h1 : locChar ψ hψ θ ≠ 1) (h : IsFJFrameT ψ d ζ (locChar ψ hψ θ) τ β γ) :
    ∃ t₀, IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β (normScale θ (fun i => τ (coef ρ (D.host.xi0⁻¹ * hQ L ζ ζ) i)) t₀) := by
  obtain ⟨t, ht⟩ := h.2.1
  refine ⟨t 0, ht.1, fun i => ?_⟩
  rw [ht.2, eq_normScale (ne_zero_of_locChar_ne_one hψ h1) (fun i hi => scale_of_isNormalFrame hψ h1 ht
    (fun _ hg => fjCharT_locGL ψ d ζ h.1 ht (Subgroup.mem_inf.1 hg).1) (fun _ hg => Subgroup.mem_inf.2 ⟨hg _, hg _⟩) h.2 hi) i.2]

theorem exists_isFJFrameT (hζ : IsLineVec L ζ) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (hθ : θ ≠ 0)
    (γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)) {t₀ : Fv D.host.F v} (h₀ : t₀ ≠ 0) :
    ∃ β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * ρ)) (Fin V.rank), IsFJFrameT ψ d ζ (locChar ψ hψ θ) τ β γ ∧
      IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β (normScale θ (fun i => τ (coef ρ (D.host.xi0⁻¹ * hQ L ζ ζ) i)) t₀) := by
  obtain ⟨β, hβ⟩ := (isSys_fj d).exists_isScaled τ γ fun i _ => normScale_ne_zero hθ
    (fun i => (map_ne_zero τ).2 (coef_ne_zero (p := ρ) (mul_ne_zero (inv_ne_zero cmHost_imaginaryGenerator_ne_zero) hζ.2) i)) h₀ i
  exact ⟨β, isFJFrameT_of_scale hψ d rfl hβ fun i _ => normScale_succ hθ _ _ i, hβ⟩

def scaleDec (y : D.host.E) (hy : y ≠ 0) : HypDec V V₀ ρ where
  e := y • d.e
  e' := (star y)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero, smul_zero]
  e'e' := by rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero, smul_zero]
  e'e := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      inv_mul_cancel₀ hy, one_smul]
  iso := d.iso
  i₀e := by rw [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by rw [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

def srcDec : HypDec V V₀ ρ := scaleDec d D.host.xi0 cmHost_imaginaryGenerator_ne_zero

theorem colN_smul {m : ℕ} (y : D.host.E) (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : ℕ) : colN (y • M) i = y • colN M i := by
  unfold colN
  split_ifs
  exacts [rfl, (smul_zero y).symm]

theorem fourierJacobiVectors_source (i : ℕ) : fourierJacobiVectors (srcDec d) i = (if i < ρ then D.host.xi0 else -D.host.xi0⁻¹) • fourierJacobiVectors d i := by
  unfold fourierJacobiVectors
  split_ifs
  · exact colN_smul _ _ _
  · rw [← inv_neg, ← GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]; exact colN_smul _ _ _

theorem isScaled_srcDec : IsScaled V V₀ τ (srcDec d).i₀ (fourierJacobiVectors (srcDec d)) γ β t ↔
    IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β fun i => t i * τ (if i < ρ then D.host.xi0 else -D.host.xi0⁻¹) := by
  refine and_congr Iff.rfl (forall_congr' fun i => Eq.congr_right ?_)
  funext y
  rw [fourierJacobiVectors_source]
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul, mul_assoc]

theorem isFJFrameS_srcDec_iff {ζ' : Fin L'.rank → D.host.E} (hz : hQ L ζ ζ = hQ L' ζ' ζ')
    (ψv : AddChar (Fv D.host.F v) Circle) : IsFJFrameS ψ (srcDec d) ζ' ψv τ β γ ↔ IsFJFrameT ψ d ζ ψv τ β γ := by
  have hx : τ D.host.xi0 ≠ 0 := (map_ne_zero τ).2 cmHost_imaginaryGenerator_ne_zero
  have hs (i : ℕ) : τ (if i < ρ then D.host.xi0 else -D.host.xi0⁻¹) ≠ 0 := by
    split_ifs <;> simp [cmHost_imaginaryGenerator_ne_zero]
  have h1 : IsAdapted V V₀ τ (srcDec d).i₀ (fourierJacobiVectors (srcDec d)) γ β ↔ IsAdapted V V₀ τ d.i₀ (fourierJacobiVectors d) γ β :=
    ⟨fun ⟨t, h⟩ => ⟨_, (isScaled_srcDec d).1 h⟩, fun ⟨t, h⟩ =>
      ⟨fun i => t i / τ (if i < ρ then D.host.xi0 else -D.host.xi0⁻¹), (isScaled_srcDec d).2 (by
        simpa only [div_mul_cancel₀ _ (hs _)] using h)⟩⟩
  refine and_congr_right fun hc => (and_congr_right fun ⟨t, ht⟩ => forall₂_congr fun g hg => Eq.congr_left ?_).trans
    (and_congr_left' h1)
  rw [fjCharS_locGL ψ _ ζ' hc ht hg.1, fjCharT_locGL ψ d ζ hc ((isScaled_srcDec d).1 ht) hg.1, hz]
  refine congrArg _ (Finset.sum_congr rfl fun i hi => congrArg (· * _) ?_)
  have h2 := ht.ne_zero (show i + 1 < c by have := Finset.mem_range.1 hi; omega)
  unfold coef
  rcases lt_trichotomy (i + 1) ρ with h | h | h
  · simp only [if_pos h, if_pos (show i < ρ by omega)]
    field_simp
  · simp only [if_neg h.not_lt, if_pos h, if_pos (show i < ρ by omega), map_neg, map_mul, map_inv₀]
    field_simp
  · simp only [if_neg h.not_gt, if_neg h.ne', if_neg (show ¬ i < ρ by omega), map_neg, map_inv₀]
    field_simp

theorem isFJFrameS_iff_of_norm {ζ' : Fin L'.rank → D.host.E}
    (hz : hQ L ζ ζ = D.host.xi0 * star D.host.xi0 * hQ L' ζ' ζ') (ψv : AddChar (Fv D.host.F v) Circle) :
    IsFJFrameS ψ d ζ' ψv τ β γ ↔ IsFJFrameT ψ d ζ ψv τ β γ := by
  refine and_congr_right fun hc => and_congr_right fun ⟨t, ht⟩ => forall₂_congr fun g hg => Eq.congr_left ?_
  rw [fjCharS_locGL ψ _ ζ' hc ht hg.1, fjCharT_locGL ψ d ζ hc ht hg.1, hz, mul_assoc, inv_mul_cancel_left₀ cmHost_imaginaryGenerator_ne_zero,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, neg_mul]

end FJ

end Normal

end GlobalTheory.LocFrame

end
