import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds

noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Lat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem afsplit_mem_stdLat (S : Subring A) (x : n → A) :
    x ∈ stdLat (n := n) (A := A) S ↔ ∀ i, x i ∈ S := by
  constructor
  · intro h i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ((Submodule.mem_pi.mp h) i (Set.mem_univ i))
    rw [← hy]
    exact y.2
  · intro h
    exact Submodule.mem_pi.mpr fun i _ => LinearMap.mem_range.mpr ⟨⟨x i, h i⟩, rfl⟩

theorem afsplit_mulVec_mem (S : Subring A) (M : Matrix n n A) (hM : ∀ i j, M i j ∈ S) (x : n → A)
    (hx : ∀ i, x i ∈ S) (i : n) : (M *ᵥ x) i ∈ S := by
  show ∑ j, M i j * x j ∈ S
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem afsplit_stab_iff (S : Subring A) (g : GL n A) :
    g ∈ stabGL (stdLat (n := n) (A := A) S) ↔
      (∀ i j, (g : Matrix n n A) i j ∈ S) ∧ (∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S) := by
  have hmem := fun x : n → A => afsplit_mem_stdLat (n := n) S x
  have hinv : ∀ x : n → A, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ ((g : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ x : n → A, (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsingle : ∀ j : n, (Pi.single j (1 : A) : n → A) ∈ stdLat (n := n) (A := A) S := by
    intro j
    rw [hmem]
    intro i
    by_cases h : i = j
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h]
      exact S.zero_mem
  have hcol : ∀ (M : Matrix n n A) (i j : n), (M *ᵥ Pi.single j (1 : A)) i = M i j := by
    intro M i j
    first
      | simp [Matrix.mulVec_single_one]
      | simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      | simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]
  constructor
  · intro hg
    have hg' : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
        (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S := hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have h1 := ((hmem _).mp ((hg' _).mp (hsingle j))) i
      rwa [hcol] at h1
    · have h1 : (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ Pi.single j 1) ∈
          stdLat (n := n) (A := A) S := by
        rw [hinv']
        exact hsingle j
      have h2 := ((hmem _).mp ((hg' _).mpr h1)) i
      rwa [hcol] at h2
  · rintro ⟨h1, h2⟩
    show ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
      (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S
    intro x
    rw [hmem, hmem]
    constructor
    · intro hx i
      exact afsplit_mulVec_mem S _ h1 x hx i
    · intro hx i
      have h3 := afsplit_mulVec_mem S _ h2 _ hx i
      rwa [hinv] at h3

theorem afsplit_one_mem (S : Subring A) (i j : n) : (1 : Matrix n n A) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Lat

section Int
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

private lemma prV_tmul_lemma_12 (a : E) (y : 𝔸) : prV (E := E) v (a ⊗ₜ[F] y) = a ⊗ₜ[F] (y v) := by
  first
    | (simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]; done)
    | (simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]; rfl)
    | simp [prV, evalV]

private lemma IE_tmul_lemma_10 (a : E) (b : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] b) = a ⊗ₜ[F] afsplitF v b := by
  show LinearMap.lTensor E (afsplitI v) (a ⊗ₜ[F] b) = _
  rw [LinearMap.lTensor_tmul]
  try rfl

private lemma eps_eq_lemma_2 : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitF v 1 := by
  show afsplitIE v ((1 : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = _
  exact IE_tmul_lemma_10 v 1 1

private lemma prV_IE_lemma (x : E ⊗[F] v.adicCompletion F) : prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [IE_tmul_lemma_10, prV_tmul_lemma_12, afsplitF_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma IE_prV_lemma_3 (x : E ⊗[F] 𝔸) : afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [prV_tmul_lemma_12, IE_tmul_lemma_10, eps_eq_lemma_2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ext w
    congr 1
    rw [show (afsplitF v 1 * y) w = afsplitF v 1 w * y w from by first | rfl | simp]
    by_cases h : w = v
    · subst h
      rw [afsplitF_self, afsplitF_self, one_mul]
    · rw [afsplitF_ne v w h, afsplitF_ne v w h, zero_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

private lemma prV_eps_lemma_4 : prV (E := E) v (afsplitEps E v) = 1 := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, prV_IE_lemma]

private lemma F_int_lemma_9 (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) :
    afsplitF v y ∈ intAd F := by
  show ∀ w, (afsplitF v y) w ∈ w.adicCompletionIntegers F
  intro w
  by_cases h : w = v
  · subst h
    rw [afsplitF_self]
    exact hy
  · rw [afsplitF_ne v w h]
    exact zero_mem _

theorem afsplit_prV_int (x : E ⊗[F] 𝔸) (hx : x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) :
    prV (E := E) v x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := by
  unfold tensInt at hx ⊢
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · apply Subring.subset_closure
      refine Set.mem_union_left _ ⟨a, ?_⟩
      simp [prV_tmul_lemma_12]
      rfl
    · apply Subring.subset_closure
      refine Set.mem_union_right _ ⟨⟨(b : 𝔸) v, b.2 v⟩, ?_⟩
      simp [prV_tmul_lemma_12]
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem afsplit_IE_int (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) :
    afsplitIE v x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  unfold tensInt at hx ⊢
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have h1 : afsplitIE v ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ((a : E) ⊗ₜ[F] (1 : 𝔸)) * ((1 : E) ⊗ₜ[F] afsplitF v 1) := by
        rw [IE_tmul_lemma_10, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [h1]
      exact mul_mem (Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩))
        (Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩))
    · show afsplitIE v ((1 : E) ⊗ₜ[F] ((b : v.adicCompletion F))) ∈ _
      rw [IE_tmul_lemma_10]
      exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v b, F_int_lemma_9 v b b.2⟩, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show afsplitIE v 1 = afsplitEps E v from rfl, eps_eq_lemma_2]
    exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩)
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem afsplit_eps_int : afsplitEps E v ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  unfold tensInt
  rw [eps_eq_lemma_2]
  exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩)

variable {n : Type} [Fintype n] [DecidableEq n]

theorem afsplitC_int (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸))
    (hM : ∀ i j, M i j ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring)
    (hN : ∀ i j, N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) (i j : n) :
    afsplitC v M N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  simp only [afsplitC, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact add_mem (afsplit_IE_int v _ (hM i j))
    (mul_mem (sub_mem (one_mem _) (afsplit_eps_int (E := E) v)) (hN i j))

end Int

section Iso
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

def afsplitKer : Subgroup (GL n (E ⊗[F] 𝔸)) := UPts σ J 𝔸 ⊓ (bc (n := n) (prV (E := E) v)).ker

private lemma sig_tmul_lemma_13 {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    sigR σ R (a ⊗ₜ[F] y) = σ a ⊗ₜ[F] y := by
  simp [sigR]

private lemma prV_sig_lemma_8 (x : E ⊗[F] 𝔸) :
    prV (E := E) v (sigR σ 𝔸 x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp only [prV_tmul_lemma_12, sig_tmul_lemma_13]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem afsplit_bc_mem (g : GL n (E ⊗[F] 𝔸)) (hg : g ∈ UPts σ J 𝔸) :
    bc (prV (E := E) v) g ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ 𝔸) (g : Matrix n n (E ⊗[F] 𝔸)) * J.map (inclE (F := F) 𝔸) *
      (g : Matrix n n (E ⊗[F] 𝔸)) = J.map (inclE (F := F) 𝔸) := hg
  show cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have hJ : (J.map (inclE (F := F) 𝔸)).map (prV (E := E) v) = J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    first
      | (simp only [Matrix.map_apply, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, prV_tmul_lemma_12]; rfl)
      | simp [inclE, prV_tmul_lemma_12]
      | simp [inclE, prV, evalV]
  have hc : (cT (sigR σ 𝔸) (g : Matrix n n (E ⊗[F] 𝔸))).map (prV (E := E) v) =
      cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v)) := by
    ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply, prV_sig_lemma_8]
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem afsplit_coe_bc_prV (g : GL n (E ⊗[F] 𝔸)) (w : HeightOneSpectrum (𝓞 F)) :
    ((bc (prV (E := E) w) g : GL n (E ⊗[F] w.adicCompletion F)) : Matrix n n (E ⊗[F] w.adicCompletion F)) =
      (g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) w) := rfl

private lemma C_map_prV_lemma_5 (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸)) :
    (afsplitC v M N).map (prV (E := E) v) = M := by
  ext i j
  simp only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, prV_IE_lemma, prV_eps_lemma_4, sub_self, zero_mul, add_zero]

theorem afsplit_ker_mem (g : GL n (E ⊗[F] 𝔸)) (hg : g ∈ UPts σ J 𝔸) :
    afsplitU v 1 g ∈ afsplitKer σ J v := by
  refine Subgroup.mem_inf.mpr ⟨afsplitU_mem v σ J 1 g (Subgroup.one_mem _) hg, ?_⟩
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [afsplit_coe_bc_prV]
  exact C_map_prV_lemma_5 v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) (g : Matrix n n (E ⊗[F] 𝔸))

theorem afsplit_ker_map (k : GL n (E ⊗[F] 𝔸)) (hk : k ∈ afsplitKer σ J v) :
    (k : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v) = 1 := by
  have h2 := (Subgroup.mem_inf.mp hk).2
  rw [MonoidHom.mem_ker] at h2
  rw [← afsplit_coe_bc_prV, h2, Units.val_one]

private lemma IE_eps_lemma_6 (x : E ⊗[F] v.adicCompletion F) :
    afsplitIE v x = afsplitEps E v * afsplitIE v x := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, ← map_mul, one_mul]

private lemma eps_idem_lemma_7 : afsplitEps E v * afsplitEps E v = afsplitEps E v := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, ← map_mul, one_mul]

theorem afsplit_left (g : GL n (E ⊗[F] 𝔸)) :
    afsplitU v (bc (prV (E := E) v) g) (afsplitU v 1 g) = g := by
  apply Units.ext
  show afsplitC v ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v))
      (afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) (g : Matrix n n (E ⊗[F] 𝔸))) =
      (g : Matrix n n (E ⊗[F] 𝔸))
  ext i j
  simp only [afsplitC, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, IE_prV_lemma_3]
  linear_combination IE_eps_lemma_6 v ((1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) +
    (g : Matrix n n (E ⊗[F] 𝔸)) i j * eps_idem_lemma_7 (E := E) v

theorem afsplit_right1 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸)) :
    bc (prV (E := E) v) (afsplitU v h k) = h := by
  apply Units.ext
  rw [afsplit_coe_bc_prV]
  exact C_map_prV_lemma_5 v (h : Matrix n n (E ⊗[F] v.adicCompletion F)) (k : Matrix n n (E ⊗[F] 𝔸))

theorem afsplit_right2 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸))
    (hk : k ∈ afsplitKer σ J v) : afsplitU v 1 (afsplitU v h k) = k := by
  have hK := afsplit_ker_map σ J v k hk
  apply Units.ext
  show afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F))
      (afsplitC v (h : Matrix n n (E ⊗[F] v.adicCompletion F)) (k : Matrix n n (E ⊗[F] 𝔸))) =
      (k : Matrix n n (E ⊗[F] 𝔸))
  ext i j
  have e1 : (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j =
      prV (E := E) v ((k : Matrix n n (E ⊗[F] 𝔸)) i j) := by
    rw [← hK, Matrix.map_apply]
  simp only [afsplitC, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [e1, IE_prV_lemma_3]
  linear_combination IE_eps_lemma_6 v ((h : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) +
    (k : Matrix n n (E ⊗[F] 𝔸)) i j * eps_idem_lemma_7 (E := E) v

def afsplitE : UPts σ J 𝔸 ≃* (UPts σ J (v.adicCompletion F) × afsplitKer σ J v) where
  toFun g := (⟨bc (prV (E := E) v) g, afsplit_bc_mem σ J v g g.2⟩,
    ⟨afsplitU v 1 g, afsplit_ker_mem σ J v g g.2⟩)
  invFun p := ⟨afsplitU v p.1 p.2, afsplitU_mem v σ J _ _ p.1.2 (Subgroup.mem_inf.mp p.2.2).1⟩
  left_inv g := Subtype.ext (afsplit_left v (g : GL n (E ⊗[F] 𝔸)))
  right_inv p := Prod.ext (Subtype.ext (afsplit_right1 v _ _))
    (Subtype.ext (afsplit_right2 σ J v _ _ p.2.2))
  map_mul' g g' := by
    refine Prod.ext (Subtype.ext (map_mul _ _ _)) (Subtype.ext ?_)
    change afsplitU v 1 ((g : GL n (E ⊗[F] 𝔸)) * (g' : GL n (E ⊗[F] 𝔸))) =
      afsplitU v 1 (g : GL n (E ⊗[F] 𝔸)) * afsplitU v 1 (g' : GL n (E ⊗[F] 𝔸))
    rw [← afsplitU_mul, one_mul]

theorem afsplitE_fst (g : UPts σ J 𝔸) :
    (((afsplitE σ J v g).1 : UPts σ J (v.adicCompletion F)) : GL n _) =
      bc (prV (E := E) v) (g : GL n (E ⊗[F] 𝔸)) := rfl

theorem afsplitE_snd (g : UPts σ J 𝔸) :
    (((afsplitE σ J v g).2 : afsplitKer σ J v) : GL n _) = afsplitU v 1 (g : GL n (E ⊗[F] 𝔸)) := rfl

theorem afsplitE_symm (p : UPts σ J (v.adicCompletion F) × afsplitKer σ J v) :
    (((afsplitE σ J v).symm p : UPts σ J 𝔸) : GL n (E ⊗[F] 𝔸)) =
      afsplitU v (p.1 : GL n (E ⊗[F] v.adicCompletion F)) (p.2 : GL n (E ⊗[F] 𝔸)) := rfl

private lemma prV_IE_ne_lemma_16 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) w (afsplitIE v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [IE_tmul_lemma_10, prV_tmul_lemma_12, afsplitF_ne v w hw, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

private lemma eps_ne_lemma_17 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) : prV (E := E) w (afsplitEps E v) = 0 := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl]
  exact prV_IE_ne_lemma_16 v w hw 1

private lemma C_map_ne_lemma_15 (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸)) :
    (afsplitC v M N).map (prV (E := E) w) = N.map (prV (E := E) w) := by
  ext i j
  simp only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, prV_IE_ne_lemma_16 v w hw, eps_ne_lemma_17 v w hw, sub_zero, one_mul, zero_add]

private lemma Z_lemma_14 (z : E ⊗[F] 𝔸)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → prV (E := E) w z = 0) :
    (1 - afsplitEps E v) * z = 0 := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left (Module.Basis.ofVectorSpace F E) z
  have hcw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → ∀ i, (c i) w = 0 := by
    intro w hw i
    have h0 := hz w hw
    have hmap : prV (E := E) w (c.sum fun i n => (Module.Basis.ofVectorSpace F E) i ⊗ₜ[F] n) =
        (Finsupp.mapRange (evalV F w) (map_zero _) c).sum
          (fun i n => (Module.Basis.ofVectorSpace F E) i ⊗ₜ[F] n) := by
      rw [Finsupp.sum_mapRange_index (fun i => by simp)]
      first | rw [map_finsuppSum] | rw [map_finsupp_sum]
      simp only [prV_tmul_lemma_12]
      try rfl
    rw [hmap] at h0
    have h1 := TensorProduct.sum_tmul_basis_left_eq_zero (Module.Basis.ofVectorSpace F E) _ h0
    have h2 := DFunLike.congr_fun h1 i
    have h3 : (evalV F w) (c i) = 0 := by simpa using h2
    exact h3
  have key : ∀ i, (1 - afsplitF v 1) * c i = 0 := by
    intro i
    ext w
    congr 1
    rw [show ((1 - afsplitF v 1) * c i) w = (1 - afsplitF v 1 w) * (c i) w from by first | rfl | simp]
    rw [show (0 : 𝔸) w = 0 from by first | rfl | simp]
    by_cases h : w = v
    · subst h
      rw [afsplitF_self, sub_self, zero_mul]
    · rw [hcw w h i, mul_zero]
  have h1 : (1 : E ⊗[F] 𝔸) - afsplitEps E v = (1 : E) ⊗ₜ[F] (1 - afsplitF v 1) := by
    rw [eps_eq_lemma_2, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
  rw [h1, Finsupp.mul_sum]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, key i, TensorProduct.tmul_zero]

theorem afsplitE_snd_eq_one (g : UPts σ J 𝔸) :
    (afsplitE σ J v g).2 = 1 ↔ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (g : GL n (E ⊗[F] 𝔸)) = 1 := by
  have e : (afsplitE σ J v g).2 = 1 ↔ afsplitU v 1 (g : GL n (E ⊗[F] 𝔸)) = 1 := by
    rw [← afsplitE_snd σ J v g]
    exact ⟨fun h => by simp [h], fun h => by
      first | exact Subtype.ext h | exact OneMemClass.coe_eq_one.mp h | simpa using h⟩
  rw [e]
  constructor
  · intro h w hw
    apply Units.ext
    rw [afsplit_coe_bc_prV]
    rw [← C_map_ne_lemma_15 v w hw (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸))]
    have h' : afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) = 1 := by
      have h3 := congrArg (fun M : GL n (E ⊗[F] 𝔸) => (M : Matrix n n (E ⊗[F] 𝔸))) h
      exact h3
    rw [h', Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  · intro h
    apply Units.ext
    show afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) ((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) = 1
    ext i j
    have hz : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
        prV (E := E) w (((g : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j - (1 : Matrix n n (E ⊗[F] 𝔸)) i j) = 0 := by
      intro w hw
      have hw' := congrArg (fun M : GL n (E ⊗[F] w.adicCompletion F) =>
        (M : Matrix n n (E ⊗[F] w.adicCompletion F)) i j) (h w hw)
      simp only [afsplit_coe_bc_prV, Matrix.map_apply, Units.val_one] at hw'
      rw [map_sub, hw', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hZ := Z_lemma_14 v _ hz
    have hI : afsplitIE v ((1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) =
        afsplitEps E v * (1 : Matrix n n (E ⊗[F] 𝔸)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact (mul_one (afsplitEps E v)).symm
      · rw [map_zero, mul_zero]
    simp only [afsplitC, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hI]
    linear_combination hZ

theorem afsplitE_level :
    ((levelAf σ J).subgroupOf (UPts σ J 𝔸)).map (afsplitE σ J v).toMonoidHom =
      ((levelV σ J v).subgroupOf (UPts σ J (v.adicCompletion F))).prod
        ((levelAf σ J).subgroupOf (afsplitKer σ J v)) := by
  have hAf : ∀ x : GL n (E ⊗[F] 𝔸), x ∈ levelAf σ J ↔ x ∈ UPts σ J 𝔸 ∧
      ((∀ i j, (x : Matrix n n (E ⊗[F] 𝔸)) i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) ∧
       (∀ i j, ((x⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j ∈
          tensInt (F := F) 𝔸 (intOE E) (intAd F))) :=
    fun x => Subgroup.mem_inf.trans (and_congr Iff.rfl (afsplit_stab_iff _ x))
  have hV : ∀ x : GL n (E ⊗[F] v.adicCompletion F), x ∈ levelV σ J v ↔
      x ∈ UPts σ J (v.adicCompletion F) ∧
      ((∀ i j, (x : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) ∧
       (∀ i j, ((x⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) :=
    fun x => Subgroup.mem_inf.trans (and_congr Iff.rfl (afsplit_stab_iff _ x))
  ext p
  obtain ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ := p
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_subgroupOf, afsplitE_symm]
  rw [hAf, hV, hAf]
  have hkU := (Subgroup.mem_inf.mp hk).1
  have h1mem : ∀ i j, (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun i j => afsplit_one_mem _ i j
  constructor
  · rintro ⟨-, hC, hCi⟩
    have hki : k⁻¹ ∈ afsplitKer σ J v := inv_mem hk
    have eh : ∀ i j, prV (E := E) v (afsplitC v (h : Matrix n n (E ⊗[F] v.adicCompletion F))
        (k : Matrix n n (E ⊗[F] 𝔸)) i j) = (h : Matrix n n (E ⊗[F] v.adicCompletion F)) i j :=
      fun i j => congrFun (congrFun (C_map_prV_lemma_5 v (h : Matrix n n (E ⊗[F] v.adicCompletion F))
        (k : Matrix n n (E ⊗[F] 𝔸))) i) j
    have ehi : ∀ i j, prV (E := E) v (afsplitC v ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) ((k⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j) =
        ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j :=
      fun i j => congrFun (congrFun (C_map_prV_lemma_5 v ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) ((k⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸))) i) j
    have ek : afsplitU v 1 (afsplitU v h k) = k := afsplit_right2 σ J v h k hk
    have eki : afsplitU v 1 (afsplitU v h⁻¹ k⁻¹) = k⁻¹ := afsplit_right2 σ J v h⁻¹ k⁻¹ hki
    refine ⟨⟨hh, fun i j => ?_, fun i j => ?_⟩, ⟨hkU, fun i j => ?_, fun i j => ?_⟩⟩
    · rw [← eh]
      exact afsplit_prV_int v _ (hC i j)
    · rw [← ehi]
      exact afsplit_prV_int v _ (hCi i j)
    · rw [← ek]
      exact afsplitC_int v _ _ h1mem hC i j
    · rw [← eki]
      exact afsplitC_int v _ _ h1mem hCi i j
  · rintro ⟨⟨-, hh1, hh2⟩, ⟨-, hk1, hk2⟩⟩
    exact ⟨afsplitU_mem v σ J h k hh hkU, fun i j => afsplitC_int v _ _ hh1 hk1 i j,
      fun i j => afsplitC_int v _ _ hh2 hk2 i j⟩

end Iso

theorem finite_adele_split_off_holds : Formalism.UG.AfSplitOff := by
  unfold AfSplitOff
  intro F E _ _ _ _ _ n _ _ σ J v
  exact ⟨↥(afsplitKer σ J v), inferInstance, (levelAf σ J).subgroupOf (afsplitKer σ J v), afsplitE σ J v,
    fun g => afsplitE_fst σ J v g, fun g => afsplitE_snd_eq_one σ J v g, afsplitE_level σ J v⟩

end Formalism.UG.P
