import Formalism.FormalDegreeBessel.StatementIO
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.FinalF

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev IOPt {n : ℕ} (ε : Fin n → Bool) : Type := {g : Matrix (Fin n) (Fin n) ℂ // inUJ ε g}

open Classical in

def ioExt {n : ℕ} (ε : Fin n → Bool) {E : Type} [Zero E] (φ : IOPt ε → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => if h : inUJ ε g then φ ⟨g, h⟩ else 0

section Core

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma io_inUJ_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inUJ ε A) (hB : inUJ ε B) :
    inUJ ε (A * B) := by
  unfold inUJ at hA hB ⊢
  calc (A * B)ᴴ * Jm ε * (A * B) = Bᴴ * (Aᴴ * Jm ε * A) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hA, hB]

lemma ioExt_at {φ : IOPt ε → E} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ioExt ε φ g = φ ⟨g, hg⟩ := by
  unfold ioExt
  rw [dif_pos hg]

lemma io_smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (hf : SmoothOnGV ε f) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).symm.trans (hfF g hg hgJ)⟩

lemma io_smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma io_smooth_add {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') : SmoothOnGV ε (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  simp only [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

lemma io_smooth_smul {f : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ) (hf : SmoothOnGV ε f) :
    SmoothOnGV ε (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgJ => ?_⟩
  simp only [hfF g hg hgJ]

private lemma Jm_mul_self_eq_oneFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq_selfFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

private lemma inUJ_exp_of_inG_formal_degree_ratio {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inG at hY
  unfold inUJ
  have hYH : Yᴴ = Jm ε * -Y * (Jm ε)⁻¹ := by
    have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
    have h1 : Yᴴ * Jm ε * Jm ε = -(Jm ε * Y) * Jm ε := by rw [eq_neg_of_add_eq_zero_left hY]
    rw [Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one] at h1
    rw [h1, hJi, Matrix.mul_neg, Matrix.neg_mul]
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_oneFormalDegreeRatio ε, Jm_mul_self_eq_oneFormalDegreeRatio ε⟩, rfl⟩
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hJu, hJi,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

private lemma inG_real_smul_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (t : ℝ) : inG ε ((t : ℂ) • X) := by
  unfold inG at hX ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma io_rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (io_inUJ_mul hg (inUJ_exp_of_inG_formal_degree_ratio (inG_real_smul_of_inG hX t)))

private lemma inG_cpart1_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp only [star_div₀, star_one, star_ofNat]
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_sub]
  abel

private lemma inG_cpart2_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [star_div₀, star_one, star_mul', hI, star_ofNat]
    ring
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_add, neg_smul]
  simp only [neg_smul, one_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio,
    Matrix.mul_one]
  abel

lemma io_eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  simp only [EabV, EcV]
  rw [io_rd_congr h (inG_cpart1_formal_degree_ratio ε _) hg, io_rd_congr h (inG_cpart2_formal_degree_ratio ε _) hg]

lemma io_eab_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  have h1 := rdSmoothV n ε E f (cpart1 ε (Matrix.single a b 1)) hf (inG_cpart1_formal_degree_ratio ε _)
  have h2 := rdSmoothV n ε E f (cpart2 ε (Matrix.single a b 1)) hf (inG_cpart2_formal_degree_ratio ε _)
  exact io_smooth_add h1 (io_smooth_smul Complex.I h2)

lemma io_eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun h => f h + c • f' h) g = EabV ε a b f g + c • EabV ε a b f' g := by
  have h1 := (rdLinV n ε E f f' (cpart1 ε (Matrix.single a b 1)) (cpart1 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart1_formal_degree_ratio ε _) (inG_cpart1_formal_degree_ratio ε _) hg).2.2
  have h2 := (rdLinV n ε E f f' (cpart2 ε (Matrix.single a b 1)) (cpart2 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart2_formal_degree_ratio ε _) (inG_cpart2_formal_degree_ratio ε _) hg).2.2
  simp only [EabV, EcV]
  rw [h1, h2, smul_add, smul_add, smul_comm Complex.I c]
  abel

lemma io_eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) g = 0 := by
  simp only [EabV, EcV, RdV, deriv_const, smul_zero, add_zero]

variable (ε E) in

def ioS : Submodule ℂ (IOPt ε → E) where
  carrier := {φ | SmoothOnGV ε (ioExt ε φ)}
  add_mem' {φ ψ} hφ hψ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.add_apply]) (io_smooth_add hφ hψ)
  zero_mem' := io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.zero_apply]) io_smooth_zero
  smul_mem' c φ hφ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.smul_apply]) (io_smooth_smul c hφ)

lemma io_mem_smooth (x : ioS ε E) : SmoothOnGV ε (ioExt ε (x : IOPt ε → E)) := x.2

def IORep (F : Matrix (Fin n) (Fin n) ℂ → E) (φ : IOPt ε → E) : Prop :=
  ∀ g (hg : inUJ ε g), F g = φ ⟨g, hg⟩

variable (ε) in

def ioT (a b : Fin n) (φ : IOPt ε → E) : IOPt ε → E := fun g => EabV ε a b (ioExt ε φ) g.1

lemma ioT_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {φ : IOPt ε → E} (h : IORep F φ) (a b : Fin n) :
    IORep (EabV ε a b F) (ioT ε a b φ) := by
  intro g hg
  exact io_eab_congr (fun g' hg' => (h g' hg').trans (ioExt_at hg').symm) a b hg

lemma ioT_mem {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (a b : Fin n) : ioT ε a b φ ∈ ioS ε E := by
  show SmoothOnGV ε (ioExt ε (ioT ε a b φ))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := ioT ε a b φ) hg).symm) (io_eab_smooth hφ a b)

lemma ioT_add {φ ψ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (hψ : ψ ∈ ioS ε E) (a b : Fin n) :
    ioT ε a b (φ + ψ) = ioT ε a b φ + ioT ε a b ψ := by
  funext g
  show EabV ε a b (ioExt ε (φ + ψ)) g.1 = EabV ε a b (ioExt ε φ) g.1 + EabV ε a b (ioExt ε ψ) g.1
  rw [io_eab_congr (f := ioExt ε (φ + ψ)) (f' := fun h => ioExt ε φ h + (1 : ℂ) • ioExt ε ψ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.add_apply, one_smul]) a b g.2,
    io_eab_lin hφ hψ 1 a b g.2, one_smul]

lemma ioT_smul {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (c : ℂ) (a b : Fin n) :
    ioT ε a b (c • φ) = c • ioT ε a b φ := by
  funext g
  show EabV ε a b (ioExt ε (c • φ)) g.1 = c • EabV ε a b (ioExt ε φ) g.1
  rw [io_eab_congr (f := ioExt ε (c • φ))
    (f' := fun h => (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) h + c • ioExt ε φ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.smul_apply, zero_add]) a b g.2,
    io_eab_lin io_smooth_zero hφ c a b g.2, io_eab_zero, zero_add]

variable (ε E) in

def ioE (a b : Fin n) : Module.End ℂ (ioS ε E) where
  toFun x := ⟨ioT ε a b x.1, ioT_mem x.2 a b⟩
  map_add' x y := Subtype.ext (ioT_add x.2 y.2 a b)
  map_smul' c x := Subtype.ext (ioT_smul x.2 c a b)

lemma ioE_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (a b : Fin n) :
    IORep (EabV ε a b F) (ioE ε E a b x).1 :=
  ioT_rep h a b

lemma io_rep_ext (x : ioS ε E) : IORep (ioExt ε x.1) x.1 := by
  intro g hg
  exact ioExt_at hg

lemma io_rep_unique {F : Matrix (Fin n) (Fin n) ℂ → E} {x y : ioS ε E} (hx : IORep F x.1)
    (hy : IORep F y.1) : x = y := by
  apply Subtype.ext
  funext g
  exact (hx g.1 g.2).symm.trans (hy g.1 g.2)

lemma io_rep_mk {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) :
    ∃ x : ioS ε E, IORep f x.1 := by
  refine ⟨⟨fun g => f g.1, ?_⟩, fun g hg => rfl⟩
  show SmoothOnGV ε (ioExt ε (fun g : IOPt ε => f g.1))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := fun g : IOPt ε => f g.1) hg).symm) hf

lemma io_rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Matrix (Fin n) (Fin n) ℂ → E}
    {x : ι → ioS ε E} (h : ∀ i, IORep (F i) (x i).1) :
    IORep (fun g => ∑ i, c i • F i g) (∑ i, c i • x i).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i g hg]

lemma io_Tm_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top (EabV ε) u a b F) (Tm (ioE ε E) u a b x).1 := by
  intro g hg
  simp only [Top, Tm]
  split_ifs with hab
  · simp only [LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add, Submodule.coe_smul,
      Pi.add_apply, Pi.smul_apply, h g hg, ioE_rep h a b g hg]
  · simp only [LinearMap.add_apply, LinearMap.zero_apply, zero_add, ioE_rep h a b g hg]

lemma io_foldr_rep (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, List.prod_nil, Module.End.one_apply]
    exact h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact io_Tm_rep ih _ _ _

lemma io_qminor_apply {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor (ioE ε E) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x := by
  simp only [qminor, LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Int.cast_smul_eq_zsmul, List.map_ofFn, Function.comp_def]

lemma io_qminor_rep {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp (EabV ε) a b u F) (qminor (ioE ε E) a b u x).1 := by
  intro g hg
  rw [io_qminor_apply]
  refine Eq.trans ?_ (io_rep_sum (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ))
    (fun σ => io_foldr_rep (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg)
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, List.map_ofFn, Function.comp_def]

variable (ε E) in
lemma io_gl : GlRel (ioE ε E) := by
  intro a b c d
  refine LinearMap.ext fun x => Subtype.ext (funext fun p => ?_)
  obtain ⟨g, hg⟩ := p
  have hF := io_rep_ext x
  have key := eabGlV n ε E (ioExt ε x.1) a b c d g (io_mem_smooth x) hg
  have r1 := ioE_rep (ioE_rep hF c d) a b g hg
  have r2 := ioE_rep (ioE_rep hF a b) c d g hg
  have r3 := ioE_rep hF a d g hg
  have r4 := ioE_rep hF c b g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← r1, ← r2, key]
  split_ifs <;> simp [r3, r4]

end Core

theorem capelli_central_holds : CapCentral := by
  intro n ε E _ _ f u c d g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := qDetCentral (Module.End ℂ (ioS ε E)) n (ioE ε E) (io_gl ε E) u c d
  calc capelli ε u (EabV ε c d f) g
      = (qminor (ioE ε E) id id u (ioE ε E c d x) : IOPt ε → E) ⟨g, hg⟩ :=
        io_qminor_rep id id u (ioE_rep hx c d) g hg
    _ = (ioE ε E c d (qminor (ioE ε E) id id u x) : IOPt ε → E) ⟨g, hg⟩ :=
        congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩) (LinearMap.congr_fun hq x)
    _ = EabV ε c d (capelli ε u f) g := (ioE_rep (io_qminor_rep id id u hx) c d g hg).symm

theorem capelli_highest_weight_holds : CapHW := by
  intro n ε E _ _ f ν hf hHW g hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hW : IsHW (ioE ε E) ν x := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a a x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a a f g' := (ioE_rep hx a a g' hg').symm
        _ = ν a • f g' := (hHW g' hg').1 a
        _ = ν a • (x : IOPt ε → E) ⟨g', hg'⟩ := by rw [hx g' hg']
        _ = ((ν a • x : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a b x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a b f g' := (ioE_rep hx a b g' hg').symm
        _ = 0 := (hHW g' hg').2 a b hab
        _ = ((0 : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
  have hu : ∀ u : ℂ, capelli ε u f g = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by
    intro u
    calc capelli ε u f g = (qminor (ioE ε E) id id u x : IOPt ε → E) ⟨g, hg⟩ :=
          io_qminor_rep id id u hx g hg
      _ = (((∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ :=
          congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩)
            (qDetHW (ioS ε E) n (ioE ε E) ν x (io_gl ε E) hW u)
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • (x : IOPt ε → E) ⟨g, hg⟩ := rfl
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by rw [hx g hg]
  refine ⟨hu, fun Y => ?_⟩
  rw [hu]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring

theorem capelli_comatrix_holds : CapComatrix := by
  intro m ε E _ _ f u i l g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := LinearMap.congr_fun
    (qComatrix (Module.End ℂ (ioS ε E)) m (ioE ε E) (io_gl ε E) u i l) x
  have hy : ∀ j : Fin (m + 1), IORep (qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u
      (Top (EabV ε) (u - (m : ℂ)) j l f))
      (qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)).1 :=
    fun j => io_qminor_rep _ _ u (io_Tm_rep hx _ j l)
  have hs := io_rep_sum (fun j : Fin (m + 1) => ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)))) hy g hg
  have hc : (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)) =
      (if i = l then qdet (ioE ε E) u else 0) x := by
    rw [← hq]
    simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Int.cast_smul_eq_zsmul ℂ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  calc (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u (Top (EabV ε) (u - (m : ℂ)) j l f) g)
      = ((∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x) :
          ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := hs
    _ = (((if i = l then qdet (ioE ε E) u else 0) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := by rw [hc]
    _ = if i = l then capelli ε u f g else 0 := by
      split_ifs with h
      · exact (io_qminor_rep id id u hx g hg).symm
      · rfl

end Formalism.QuantumDeterminants
