import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorMultiplication
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation

noncomputable section

namespace GlobalTheory.FontCmp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

theorem exists_liftAdd {R M N Z : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [AddCommGroup Z] (f : M → N → Z)
    (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n) (h2 : ∀ m n n', f m (n + n') = f m n + f m n')
    (h3 : ∀ (r : R) m n, f (r • m) n = f m (r • n)) :
    ∃ F : M ⊗[R] N →+ Z, ∀ m n, F (m ⊗ₜ n) = f m n :=
  ⟨liftAddHom (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)) h3, fun _ _ => rfl⟩

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Tools

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

variable (LL) in

def mB (b : B) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

@[simp] theorem mB_tmul (b b' : B) (v : V) : mB LL b (v ⊗ₜ[Qp] b') = v ⊗ₜ[Qp] (b * b') := by
  simp [mB]

theorem mulVB_eq (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (LL := LL) c x = mB LL (algebraMap K₀ B c) x := rfl

theorem mB_mul (b b' : B) (x : V ⊗[Qp] B) : mB LL (b * b') x = mB LL b (mB LL b' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [mul_assoc]
  | add a c ha hc => simp only [map_add, ha, hc]

theorem mB_add (b b' : B) (x : V ⊗[Qp] B) : mB LL (b + b') x = mB LL b x + mB LL b' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [add_mul, tmul_add]
  | add a c ha hc => simp only [map_add, ha, hc]; abel

theorem mB_one (x : V ⊗[Qp] B) : mB LL (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add a c ha hc => simp only [map_add, ha, hc]

theorem comm_smulB (b : B) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • x) = mB LL b (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add, ha, hc]

def mK (ρ : Representation LL G V) (c : K₀) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ) :=
  (mB LL (algebraMap K₀ B c)).restrict (fun x hx => by
    rw [CrystallineSubrepresentation.mem_Dcris] at hx ⊢
    intro g
    rw [← mulVB_eq, CrystallineSubrepresentation.actVB_mulVB, hx])

@[simp] theorem coe_mK (ρ : Representation LL G V) (c : K₀) (d : ↥(Dcris PD ρ)) :
    (mK PD ρ c d : V ⊗[Qp] B) = mB LL (algebraMap K₀ B c) d := rfl

theorem cmp_ind {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {P : V ⊗[Qp] B → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hb : ∀ (b : B) (d : ↥(Dcris PD ρ)), P (mB LL b d)) (x : V ⊗[Qp] B) : P x := by
  obtain ⟨u, hu⟩ := h.2 ((TensorProduct.comm Qp B V).symm x)
  have : x = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ u) := by rw [hu]; simp
  subst this
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul b d =>
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    exact hb b ⟨_, d.2⟩
  | add a c ha hc => simpa only [map_add] using hadd _ _ ha hc

theorem cmp_lift {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {Z : Type} [AddCommGroup Z] (f : B → ↥(Dcris PD ρ) → Z)
    (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n) (h2 : ∀ m n n', f m (n + n') = f m n + f m n')
    (h3 : ∀ (c : K₀) b d, f (algebraMap K₀ B c * b) d = f b (mK PD ρ c d)) :
    ∃ F : V ⊗[Qp] B →+ Z, ∀ (b : B) (d : ↥(Dcris PD ρ)), F (mB LL b d) = f b d := by
  obtain ⟨F, hF⟩ := exists_liftAdd (R := K₀)
    (fun (b : B) (d : ↥(CrystallineSubrepresentation.DcrisK₀ PD ρ)) => f b ⟨TensorProduct.comm Qp B V d, d.2⟩)
    (fun m m' n => h1 m m' _)
    (fun m n n' => by rw [← h2]; congr 1; ext; simp)
    (fun r m n => by
      rw [Algebra.smul_def, h3]; congr 1; ext
      simp only [coe_mK, Submodule.coe_smul]
      rw [CrystallineSubrepresentation.comm_smul (LL := LL), mulVB_eq])
  let e := LinearEquiv.ofBijective _ h
  refine ⟨(F.comp e.symm.toLinearMap.toAddMonoidHom).comp
    (TensorProduct.comm Qp B V).symm.toLinearMap.toAddMonoidHom, fun b d => ?_⟩
  let d' : ↥(CrystallineSubrepresentation.DcrisK₀ PD ρ) := ⟨(TensorProduct.comm Qp B V).symm d, by
    change TensorProduct.comm Qp B V ((TensorProduct.comm Qp B V).symm d) ∈ Dcris PD ρ
    simp⟩
  have he : e.symm ((TensorProduct.comm Qp B V).symm (mB LL b d)) = b ⊗ₜ d' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]
    change _ = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ (b ⊗ₜ d'))
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    simp [d']
  change F (e.symm ((TensorProduct.comm Qp B V).symm (mB LL b d))) = _
  rw [he, hF]
  congr 1
  ext
  simp [d']

include PD in
theorem exists_retr : ∃ lam : B →ₗ[K₀] K₀, lam 1 = 1 := by
  have : (1 : B) ≠ 0 := by
    intro h
    apply PD.not_mem_filtration_two
    rw [← mul_one PD.t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K₀ this
  exact ⟨(f 1)⁻¹ • f, by simp [hf]⟩

theorem exists_proj {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ)) :
    ∃ (lam : B → K₀) (π : V ⊗[Qp] B →+ ↥(Dcris PD ρ)),
      (∀ (b : B) (d : ↥(Dcris PD ρ)), π (mB LL b d) = mK PD ρ (lam b) d) ∧
      (∀ d : ↥(Dcris PD ρ), π d = d) ∧ (∀ (a : LL) x, π (a • x) = a • π x) ∧
      (∀ (c : K₀) x, π (mB LL (algebraMap K₀ B c) x) = mK PD ρ c (π x)) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  obtain ⟨π, hπ⟩ := cmp_lift PD h (fun b d => mK PD ρ (lam b) d)
    (fun m m' n => by ext; simp [mB_add]) (fun m n n' => by simp)
    (fun c b d => by
      ext
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
      simp [mB_mul])
  refine ⟨lam, π, hπ, fun d => ?_, fun a x => ?_, fun c x => ?_⟩
  · have := hπ 1 d
    rw [mB_one, hl] at this
    rw [this]; ext; simp [mB_one]
  · induction x using cmp_ind PD h with
    | h0 => simp
    | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
    | hb b d => rw [← map_smul, ← Submodule.coe_smul, hπ, hπ, map_smul]
  · induction x using cmp_ind PD h with
    | h0 => simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
    | hb b d =>
      rw [← mB_mul, hπ, hπ, ← Algebra.smul_def, map_smul]
      ext
      simp [mB_mul]

theorem prod_mB_left (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (mB LL b x ⊗ₜ[LL] y) = mB LL b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_assoc]

theorem prod_mB_right (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] mB LL b y) = mB LL b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_left_comm]

theorem act_prod (ρ : Representation LL G V) (ρ' : Representation LL G V') (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (ρ.tprod ρ') g (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) =
      CrystallineSubrepresentation.prodB (actVB PD ρ g x ⊗ₜ[LL] actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, actVB]

theorem prod_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    CrystallineSubrepresentation.prodB (LL := LL) ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B)) ∈ Dcris PD (ρ.tprod ρ') := by
  rw [CrystallineSubrepresentation.mem_Dcris]
  intro g
  rw [act_prod, (CrystallineSubrepresentation.mem_Dcris PD ρ x).1 x.2, (CrystallineSubrepresentation.mem_Dcris PD ρ' y).1 y.2]

theorem mulDcris_tmul {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    TensorMultiplication.mulDcris PD ρ ρ' (x ⊗ₜ y) =
      CrystallineSubrepresentation.prodB (LL := LL) ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B)) := rfl

theorem range_le {ρ : Representation LL G V} {ρ' : Representation LL G V'} :
    LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') ≤ Dcris PD (ρ.tprod ρ') := by
  rintro _ ⟨w, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
  | tmul x y => rw [mulDcris_tmul]; exact prod_mem PD x y

theorem range_eq {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    (h' : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ'))
    (h'' : Function.Bijective (CrystallineSubrepresentation.comparison PD (ρ.tprod ρ'))) :
    LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ') := by
  refine le_antisymm (range_le PD) fun z hz => ?_
  obtain ⟨lam, π, hπ, hid, -, -⟩ := exists_proj PD h''
  have key : ∀ (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B),
      (π (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) : (V ⊗[LL] V') ⊗[Qp] B) ∈
        LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') := by
    intro x y
    induction x using cmp_ind PD h with
    | h0 => simp
    | hadd a c ha hc =>
      simp only [add_tmul, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
    | hb b d =>
      induction y using cmp_ind PD h' with
      | h0 => simp
      | hadd a c ha hc =>
        simp only [tmul_add, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
      | hb b' d' =>
        rw [prod_mB_left, prod_mB_right, ← mB_mul]
        have := hπ (b * b') ⟨_, prod_mem PD d d'⟩
        simp only at this
        rw [this, coe_mK]
        exact ⟨mK PD ρ (lam (b * b')) d ⊗ₜ d', by rw [mulDcris_tmul, coe_mK, prod_mB_left]⟩
  have all : ∀ z : (V ⊗[LL] V') ⊗[Qp] B, (π z : (V ⊗[LL] V') ⊗[Qp] B) ∈
      LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
    | tmul u b =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc =>
        simp only [add_tmul, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
      | tmul v v' =>
        have := key (v ⊗ₜ b) (v' ⊗ₜ 1)
        rwa [CrystallineSubrepresentation.prodB_tmul, mul_one] at this
  have := all z
  rwa [show π z = ⟨z, hz⟩ from hid ⟨z, hz⟩] at this

theorem bal_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'} (c : K₀)
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    mK PD ρ c x ⊗ₜ[LL] y - x ⊗ₜ[LL] mK PD ρ' c y ∈ TensorMultiplication.balK PD ρ ρ' :=
  Submodule.subset_span ⟨c, x, _, y, _, rfl, rfl, rfl⟩

theorem ker_eq {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    (h' : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ')) :
    LinearMap.ker (TensorMultiplication.mulDcris PD ρ ρ') = TensorMultiplication.balK PD ρ ρ' := by
  refine le_antisymm ?_ ?_
  swap
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, x, cx, y, cy, hx, hy, rfl⟩
    change TensorMultiplication.mulDcris PD ρ ρ' _ = 0
    rw [map_sub, mulDcris_tmul, mulDcris_tmul, hx, hy, mulVB_eq, mulVB_eq, prod_mB_left,
      prod_mB_right, sub_self]
  obtain ⟨lam, π, hπ, hid, hπa, hπc⟩ := exists_proj PD h
  let q := (TensorMultiplication.balK PD ρ ρ').mkQ
  have hq : ∀ c x y, q (mK PD ρ c x ⊗ₜ y) = q (x ⊗ₜ mK PD ρ' c y) := fun c x y => by
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).2 (bal_mem PD c x y)
  have e1 := fun x : V ⊗[Qp] B => cmp_lift PD h' (fun b d' => q (π (mB LL b x) ⊗ₜ d'))
    (fun m m' n => by simp only [mB_add, map_add, add_tmul])
    (fun m n n' => by simp only [map_add, tmul_add])
    (fun c b d => by rw [mB_mul, hπc, hq])
  choose γ hγ using e1
  have γadd : ∀ x x' y, γ (x + x') y = γ x y + γ x' y := by
    intro x x' y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [map_add, ha, hc]; abel
    | hb b d => simp only [hγ, map_add, add_tmul]
  have γsmul : ∀ (a : LL) x y, γ (a • x) y = γ x (a • y) := by
    intro a x y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [smul_add, map_add, ha, hc]
    | hb b d =>
      rw [← map_smul, ← Submodule.coe_smul, hγ, hγ, map_smul, hπa, smul_tmul]
  have γB : ∀ (b : B) x y, γ (mB LL b x) y = γ x (mB LL b y) := by
    intro a x y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [map_add, ha, hc]
    | hb b d => rw [← mB_mul, hγ, hγ, ← mB_mul, mul_comm]
  have e2 := fun b : B => exists_liftAdd (R := LL)
    (fun (v : V) (v' : V') => γ (v ⊗ₜ[Qp] b) (v' ⊗ₜ[Qp] (1 : B)))
    (fun m m' n => by simp only [add_tmul, γadd])
    (fun m n n' => by simp only [add_tmul, map_add])
    (fun r m n => by rw [← smul_tmul', γsmul, smul_tmul'])
  choose Φ₁ hΦ₁ using e2
  obtain ⟨Φ, hΦ⟩ := exists_liftAdd (R := Qp) (fun (u : V ⊗[LL] V') (b : B) => Φ₁ b u)
    (fun m m' n => by simp only [map_add])
    (fun u b b' => by
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]; abel
      | tmul v v' => simp only [hΦ₁, tmul_add, γadd])
    (fun r u b => by
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [smul_add, map_add, ha, hc]
      | tmul v v' => rw [smul_tmul', hΦ₁, hΦ₁, smul_tmul])
  have γ0 : ∀ y, γ 0 y = 0 := fun y => by
    have := γadd 0 0 y
    rw [add_zero] at this
    simpa using this
  have hprod : ∀ x y, Φ (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) = γ x y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp [γ0]
    | add a c ha hc => simp only [map_add, add_tmul, ha, hc, γadd]
    | tmul v c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
      | tmul v' c' =>
        rw [CrystallineSubrepresentation.prodB_tmul, hΦ, hΦ₁, mul_comm, ← mB_tmul (LL := LL), γB, mB_tmul, mul_one]
  have hall : ∀ w, Φ (TensorMultiplication.mulDcris PD ρ ρ' w) = q w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      rw [mulDcris_tmul, hprod, ← mB_one (LL := LL) (y : V' ⊗[Qp] B), hγ, mB_one, hid]
  intro w hw
  have := hall w
  rw [LinearMap.mem_ker.1 hw, map_zero] at this
  exact (Submodule.Quotient.mk_eq_zero _).1 this.symm

theorem unit_eq : Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  ext x
  rw [CrystallineSubrepresentation.mem_Dcris]
  constructor
  · intro hx

    let ctr : (LL →ₗ[Qp] Qp) → (LL ⊗[Qp] B →ₗ[Qp] B) := fun f =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B f
    have hc : ∀ f g y, ctr f (actVB PD (Representation.trivial LL G LL) g y) =
        PD.actB g (ctr f y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul a b =>
        simp only [ctr, actVB]
        simp
        rw [← IsScalarTower.algebraMap_smul K₀ (f a) b, map_smul, IsScalarTower.algebraMap_smul]
    let r : B →ₗ[Qp] K₀ := lam.restrictScalars Qp
    let j : K₀ →ₗ[Qp] B := (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap
    have hr : ∀ f y, ctr f (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) j
        (LinearMap.lTensor LL r y)) = j (r (ctr f y)) := by
      intro f y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul a b => simp [ctr]
    have hsep : ∀ y : LL ⊗[Qp] B, (∀ f, ctr f y = 0) → y = 0 := by
      intro y hy
      classical
      let bs := Module.Free.chooseBasis Qp LL
      apply (TensorProduct.comm Qp LL B).injective
      apply (TensorProduct.equivFinsuppOfBasisRight bs).injective
      ext i
      have : ∀ y : LL ⊗[Qp] B, TensorProduct.equivFinsuppOfBasisRight bs
          (TensorProduct.comm Qp LL B y) i = ctr (bs.coord i) y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]
        | tmul a b => simp [ctr]
      simp [this, hy]
    refine ⟨LinearMap.lTensor LL r x, ?_⟩
    rw [← sub_eq_zero]
    apply hsep
    intro f
    rw [map_sub, hr]
    obtain ⟨c, hc'⟩ := PD.invB (ctr f x) (fun g => by rw [← hc, hx])
    rw [← hc', sub_eq_zero]
    change algebraMap K₀ B (lam (algebraMap K₀ B c)) = _
    rw [Algebra.algebraMap_eq_smul_one c, map_smul, hl]
    simp [Algebra.algebraMap_eq_smul_one]
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul a b => simp [actVB]

variable (LL V) in

def actKK (τ : K₀ →ₐ[Qp] LL) : K₀ ⊗[Qp] K₀ →+ (V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) :=
  liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
      (fun c => τ a • mB LL (algebraMap K₀ B c))
      (fun c c' => by ext x; simp [mB_add, add_mul, tmul_add]))
      (fun a a' => by ext c x; simp [add_smul]))
    (fun r a c => by
      ext v b
      simp only [AddMonoidHom.mk'_apply, map_smul, AlgebraTensorModule.curry_apply,
        LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.smul_apply, mB_tmul]
      rw [smul_assoc, smul_comm r, ← tmul_smul, ← smul_mul_assoc, Algebra.smul_def r c, map_mul,
        ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def])

theorem actKK_tmul (τ : K₀ →ₐ[Qp] LL) (a c : K₀) (x : V ⊗[Qp] B) :
    actKK LL V τ (a ⊗ₜ c) x = τ a • mB LL (algebraMap K₀ B c) x := rfl

theorem mem_DcrisL (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧ ∀ c : K₀, mB LL (algebraMap K₀ B c) x = τ c • x := by
  simp [DcrisL, Submodule.mem_iInf, sub_eq_zero, mulVB_eq]

theorem actKK_mul (τ : K₀ →ₐ[Qp] LL) (s t : K₀ ⊗[Qp] K₀) (x : V ⊗[Qp] B) :
    actKK LL V τ (s * t) x = actKK LL V τ s (actKK LL V τ t x) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [add_mul, map_add, LinearMap.add_apply, ha, hc]
  | tmul a c =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [mul_add, map_add, LinearMap.add_apply, ha, hc]
    | tmul a' c' => simp [actKK_tmul, mB_mul, smul_smul, mul_comm]

theorem actKK_mem (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (t : K₀ ⊗[Qp] K₀)
    (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) : actKK LL V τ t x ∈ Dcris PD ρ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hc
  | tmul a c => rw [actKK_tmul]; exact Submodule.smul_mem _ _ (mK PD ρ c ⟨x, hx⟩).2

theorem actKK_eigen (τ : K₀ →ₐ[Qp] LL) (t : K₀ ⊗[Qp] K₀) (x : V ⊗[Qp] B)
    (hx : ∀ c : K₀, mB LL (algebraMap K₀ B c) x = τ c • x) :
    actKK LL V τ t x = τ (Algebra.TensorProduct.lmul' Qp t) • x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc, add_smul]
  | tmul a c => simp [actKK_tmul, hx, smul_smul]

theorem prod_actKK_left (τ : K₀ →ₐ[Qp] LL) (t : K₀ ⊗[Qp] K₀) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (actKK LL V τ t x ⊗ₜ[LL] y) =
      actKK LL (V ⊗[LL] V') τ t (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, add_tmul, ha, hc]
  | tmul a c => rw [actKK_tmul, actKK_tmul, ← smul_tmul', map_smul, prod_mB_left]

theorem prod_actKK_right (τ : K₀ →ₐ[Qp] LL) (t : K₀ ⊗[Qp] K₀) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] actKK LL V' τ t y) =
      actKK LL (V ⊗[LL] V') τ t (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, tmul_add, ha, hc]
  | tmul a c => rw [actKK_tmul, actKK_tmul, tmul_smul, map_smul, prod_mB_right]

theorem letter_of_ker [Algebra.IsSeparable Qp K₀]
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hr : LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ'))
    (hk : LinearMap.ker (TensorMultiplication.mulDcris PD ρ ρ') = TensorMultiplication.balK PD ρ ρ') (τ : K₀ →ₐ[Qp] LL) :
    Function.Injective ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) ∧
      LinearMap.range ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) =
        DcrisL PD (ρ.tprod ρ') τ := by
  haveI := PD.finK₀
  haveI : Algebra.FormallyUnramified Qp K₀ := Algebra.FormallyUnramified.of_isSeparable Qp K₀
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := Qp)
    (S := K₀)).1 inferInstance
  have hE : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B) (c : K₀),
      mB LL (algebraMap K₀ B c) (actKK LL U τ t x) = τ c • actKK LL U τ t x := by
    intro U _ _ _ _ x c
    have h1 : actKK LL U τ ((1 : K₀) ⊗ₜ[Qp] c * t) x = actKK LL U τ (c ⊗ₜ[Qp] (1 : K₀) * t) x := by
      rw [sub_eq_zero.1 ((sub_mul _ _ _).symm.trans (ht c))]
    rw [actKK_mul, actKK_mul, actKK_tmul, actKK_tmul] at h1
    simpa [mB_one] using h1
  have hI : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B), (∀ c : K₀, mB LL (algebraMap K₀ B c) x = τ c • x) →
      actKK LL U τ t x = x := by
    intro U _ _ _ _ x hx
    rw [actKK_eigen τ t x hx, ht1, map_one, one_smul]
  have hC : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B) (c : K₀),
      actKK LL U τ t (mB LL (algebraMap K₀ B c) x) = τ c • actKK LL U τ t x := by
    intro U _ _ _ _ x c
    have h1 : actKK LL U τ (t * (1 : K₀) ⊗ₜ[Qp] c) x = actKK LL U τ ((1 : K₀) ⊗ₜ[Qp] c * t) x := by
      rw [mul_comm]
    rw [actKK_mul, actKK_mul, actKK_tmul, actKK_tmul, hE] at h1
    simpa using h1
  let p : ↥(Dcris PD ρ) →ₗ[LL] ↥(DcrisL PD ρ τ) :=
    (actKK LL V τ t).restrict fun x hx => (mem_DcrisL PD ρ τ _).2 ⟨actKK_mem PD ρ τ t x hx, hE V x⟩
  let p' : ↥(Dcris PD ρ') →ₗ[LL] ↥(DcrisL PD ρ' τ) :=
    (actKK LL V' τ t).restrict
      fun x hx => (mem_DcrisL PD ρ' τ _).2 ⟨actKK_mem PD ρ' τ t x hx, hE V' x⟩
  let i : ↥(DcrisL PD ρ τ) →ₗ[LL] ↥(Dcris PD ρ) := Submodule.inclusion inf_le_left
  let i' : ↥(DcrisL PD ρ' τ) →ₗ[LL] ↥(Dcris PD ρ') := Submodule.inclusion inf_le_left
  have hfac : ∀ w, ((CrystallineSubrepresentation.prodB (LL := LL)).comp
      (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) w =
      TensorMultiplication.mulDcris PD ρ ρ' (TensorProduct.map i i' w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y => rfl
  have hpi : ∀ w, TensorProduct.map p p' (TensorProduct.map i i' w) = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      rw [map_tmul, map_tmul]
      congr 1
      · exact Subtype.ext (hI V x ((mem_DcrisL PD ρ τ _).1 x.2).2)
      · exact Subtype.ext (hI V' y ((mem_DcrisL PD ρ' τ _).1 y.2).2)
  have hbal : TensorMultiplication.balK PD ρ ρ' ≤ LinearMap.ker (TensorProduct.map p p') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, x, cx, y, cy, hx, hy, rfl⟩
    change TensorProduct.map p p' _ = 0
    have h1 : p cx = τ c • p x := Subtype.ext (by
      change actKK LL V τ t (cx : V ⊗[Qp] B) = τ c • actKK LL V τ t (x : V ⊗[Qp] B)
      rw [hx, mulVB_eq, hC])
    have h2 : p' cy = τ c • p' y := Subtype.ext (by
      change actKK LL V' τ t (cy : V' ⊗[Qp] B) = τ c • actKK LL V' τ t (y : V' ⊗[Qp] B)
      rw [hy, mulVB_eq, hC])
    rw [map_sub, map_tmul, map_tmul, h1, h2, smul_tmul, sub_self]
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, le_antisymm ?_ fun z hz => ?_⟩
  · rw [hfac, ← LinearMap.mem_ker, hk] at hw
    rw [← hpi w]
    exact hbal hw
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
    | tmul x y =>
      rw [mem_DcrisL]
      refine ⟨prod_mem PD (i x) (i' y), fun c => ?_⟩
      change mB LL _ (CrystallineSubrepresentation.prodB ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B))) =
        τ c • CrystallineSubrepresentation.prodB ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B))
      rw [← prod_mB_left, ((mem_DcrisL PD ρ τ _).1 x.2).2, ← smul_tmul', map_smul]
  · obtain ⟨hz1, hz2⟩ := (mem_DcrisL PD _ τ _).1 hz
    rw [← hr] at hz1
    obtain ⟨w, rfl⟩ := hz1
    refine ⟨TensorProduct.map p p' w, ?_⟩
    rw [← hI _ _ hz2]
    clear hz hz2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      change CrystallineSubrepresentation.prodB (LL := LL) (actKK LL V τ t (x : V ⊗[Qp] B) ⊗ₜ[LL]
        actKK LL V' τ t (y : V' ⊗[Qp] B)) = _
      rw [mulDcris_tmul, prod_actKK_left, prod_actKK_right, hI _ _ (hE _ _)]

end Tools

theorem inv_iff : CrystallineSubrepresentation.InvariantsEq PD ↔ TensorMultiplication.InvB PD := Iff.rfl

variable (LL : Type) [Field LL] [Algebra Qp LL]

theorem dimLe_iff : CrystallineSubrepresentation.DimLe PD LL ↔ TensorMultiplication.DcrisFinite PD LL ∧ FontaineLe PD LL := and_comm

theorem comparison_iff : CrystallineSubrepresentation.ComparisonBij PD LL ↔ TensorMultiplication.Comparison PD LL := Iff.rfl

theorem sub_iff : CrystallineSubrepresentation.SubCrys PD LL ↔ TensorMultiplication.CrysSub PD LL := Iff.rfl

theorem quot_iff : CrystallineSubrepresentation.QuotCrys PD LL ↔ TensorMultiplication.CrysQuot PD LL := Iff.rfl

theorem sum_iff : CrystallineSubrepresentation.SumCrys PD LL ↔ TensorMultiplication.CrysSum PD LL := Iff.rfl

theorem tensor_iff : CrystallineSubrepresentation.TensorCrys PD LL ↔ TensorMultiplication.CrysTensor PD LL := Iff.rfl

theorem dual_iff : CrystallineSubrepresentation.DualCrys PD LL ↔ TensorMultiplication.CrysDual PD LL := Iff.rfl

theorem exact_iff : CrystallineSubrepresentation.DcrisExact PD LL ↔ TensorMultiplication.DcrisExact PD LL := by
  refine forall_congr' fun V₀ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₀ =>
    forall_congr' fun V₁ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₁ =>
    forall_congr' fun V₂ => forall₄_congr fun _ _ _ _ => forall₂_congr fun _ ρ₂ =>
    forall₄_congr fun i p hi hp => forall₃_congr fun _ _ _ => forall₃_congr fun _ _ _ =>
    and_congr ?_ (and_congr ?_ ?_)
  · rw [injective_iff_map_eq_zero]
    exact ⟨fun h x hx h0 => congrArg Subtype.val (h ⟨x, hx⟩ (Subtype.ext h0)),
      fun h x h0 => Subtype.ext (h x x.2 (congrArg Subtype.val h0))⟩
  · constructor
    · intro h
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨CrystallineSubrepresentation.tensorB_mem PD hi x hx,
          congrArg Subtype.val ((h (CrystallineSubrepresentation.DcrisMap PD hi ⟨x, hx⟩)).2 ⟨_, rfl⟩)⟩
      · rintro ⟨hy, h0⟩
        obtain ⟨x, hx⟩ := (h ⟨y, hy⟩).1 (Subtype.ext h0)
        exact ⟨x, x.2, congrArg Subtype.val hx⟩
    · intro h y
      constructor
      · intro h0
        have : (y : V₁ ⊗[Qp] B) ∈ (Dcris PD ρ₀).map (TensorMultiplication.mapVB B i) := by
          rw [h]; exact ⟨y.2, congrArg Subtype.val h0⟩
        obtain ⟨x, hx, e⟩ := this
        exact ⟨⟨x, hx⟩, Subtype.ext e⟩
      · rintro ⟨x, rfl⟩
        have : TensorMultiplication.mapVB B i x ∈ (Dcris PD ρ₀).map (TensorMultiplication.mapVB B i) := ⟨x, x.2, rfl⟩
        rw [h] at this
        exact Subtype.ext this.2
  · constructor
    · intro h
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact CrystallineSubrepresentation.tensorB_mem PD hp x hx
      · intro hy
        obtain ⟨x, hx⟩ := h ⟨y, hy⟩
        exact ⟨x, x.2, congrArg Subtype.val hx⟩
    · intro h y
      have : (y : V₂ ⊗[Qp] B) ∈ (Dcris PD ρ₁).map (TensorMultiplication.mapVB B p) := by rw [h]; exact y.2
      obtain ⟨x, hx, e⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩

theorem letter_iff : CrystallineSubrepresentation.LetterDim PD LL ↔ TensorMultiplication.LetterDim PD LL := by
  refine forall_congr' fun _ => forall_congr' fun V => forall₄_congr fun _ _ _ _ =>
    forall₃_congr fun _ ρ _ => forall_congr' fun τ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.1 h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ h0)

theorem dcrisTensor_of_comparison (hc : CrystallineSubrepresentation.ComparisonBij PD LL) (ht : CrystallineSubrepresentation.TensorCrys PD LL) :
    TensorMultiplication.DcrisTensor PD LL := fun V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h' =>
  ⟨range_eq PD (hc V ρ h) (hc V' ρ' h') (hc _ _ (ht V ρ V' ρ' h h')),
    ker_eq PD (hc V ρ h) (hc V' ρ' h')⟩

theorem dcrisTensor_letters [Algebra.IsSeparable Qp K₀] (h : TensorMultiplication.DcrisTensor PD LL) :
    CrystallineSubrepresentation.DcrisTensor PD LL :=
  ⟨unit_eq PD, fun V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' hρ hρ' =>
    ⟨(h V ρ V' ρ' hρ hρ').1, letter_of_ker PD (h V ρ V' ρ' hρ hρ').1 (h V ρ V' ρ' hρ hρ').2⟩⟩

theorem formalism_iff : CrystallineSubrepresentation.FormalismFor PD LL ↔ TensorMultiplication.FormalismAt PD LL :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨(inv_iff PD).1 a, (dimLe_iff PD LL).1 b,
      (comparison_iff PD LL).1 c, (sub_iff PD LL).1 d, (quot_iff PD LL).1 e, (sum_iff PD LL).1 f,
      (tensor_iff PD LL).1 g, (dual_iff PD LL).1 h, (exact_iff PD LL).1 i,
      dcrisTensor_of_comparison PD LL c g, (letter_iff PD LL).1 j⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, _, j⟩ => ⟨(inv_iff PD).2 a, (dimLe_iff PD LL).2 b,
      (comparison_iff PD LL).2 c, (sub_iff PD LL).2 d, (quot_iff PD LL).2 e, (sum_iff PD LL).2 f,
      (tensor_iff PD LL).2 g, (dual_iff PD LL).2 h, (exact_iff PD LL).2 i, (letter_iff PD LL).2 j⟩⟩

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

theorem fontaineFormalism_equiv : CrystallineSubrepresentation.FontaineFormalism l P ↔ TensorMultiplication.FontaineFormalism l P :=
  (CrystallineSubrepresentation.fontaineFormalism_iff l P).trans
    (forall₂_congr fun K LL => formalism_iff (P.PD K) ↥LL.1)

theorem fontaineFormalismTensor_equiv :
    CrystallineSubrepresentation.FontaineFormalismTensor l P ↔ TensorMultiplication.FontaineFormalism l P :=
  ⟨fun h => (fontaineFormalism_equiv l P).1 h.1, fun h => ⟨(fontaineFormalism_equiv l P).2 h,
    fun K LL => by
      haveI := (P.PD K).finK₀
      exact dcrisTensor_letters (P.PD K) ↥LL.1 (h K LL).2.2.2.2.2.2.2.2.2.1⟩⟩

end GlobalTheory.FontCmp
