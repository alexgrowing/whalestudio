import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem mAct_apply {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_mul {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) : (mAct (A * B) : (ι → V) →ₗ[ℂ] _) = mAct A ∘ₗ mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [LinearMap.comp_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem mAct_smul {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ℂ) (A : Matrix ι' ι ℂ) :
    (mAct (a • A) : (ι → V) →ₗ[ℂ] _) = a • mAct A := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]

theorem mAct_sub {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι' ι ℂ) :
    (mAct (A - B) : (ι → V) →ₗ[ℂ] _) = mAct A - mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.sub_apply, Pi.sub_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem mAct_one {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] :
    (mAct (1 : Matrix ι ι ℂ) : (ι → V) →ₗ[ℂ] _) = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, Matrix.one_apply]

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f)
    (x : M X) : f (cas X x) = cas Y (f x) := by
  have h : ∀ Z x, f (L X Z x) = L Y Z (f x) := fun Z x => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) x
  simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, h]

def cM (n : ℕ) : Matrix Unit (Fin n × Fin n) ℂ := fun _ p => if p.1 = p.2 then 1 else 0

theorem cM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Aᵀ * B = 1) :
    cM n * (A ⊗ₖ B) = (1 : Matrix Unit Unit ℂ) * cM n := by
  rw [Matrix.one_mul]
  ext _ ⟨c, d⟩
  have := congrFun (congrFun h c) d
  simp only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] at this
  simp only [Matrix.mul_apply, cM, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, kroneckerMap_apply, this]

theorem cM_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) := by
  refine hM k r _ _ B _ fun g hg => ?_
  have hu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  cases b
  · exact cM_mul (A := g) (B := (g⁻¹)ᵀ) (by rw [← transpose_mul, Matrix.nonsing_inv_mul g hu, transpose_one])
  · exact cM_mul (A := (g⁻¹)ᵀ) (B := g) (by rw [transpose_transpose, Matrix.nonsing_inv_mul g hu])

theorem casimir_kronecker_sum (n : ℕ) :
    (∑ a : Fin n, ∑ b : Fin n, Matrix.single a b (1 : ℂ) ⊗ₖ (-(Matrix.single b a (1 : ℂ))ᵀ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) ∧
    (∑ a : Fin n, ∑ b : Fin n, (-(Matrix.single a b (1 : ℂ))ᵀ) ⊗ₖ Matrix.single b a (1 : ℂ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) := by
  constructor <;> ext ⟨c, d⟩ ⟨c', d'⟩ <;>
    simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.neg_apply,
      transpose_apply, Matrix.smul_apply, Matrix.mul_apply, cM, Matrix.single_apply] <;>
    by_cases e1 : c = d <;> by_cases e2 : c' = d' <;> simp [e1, e2, ite_and, eq_comm]

theorem qMat_vr (hS : StdD) (b : Bool) :
    qMat (vr k r b) (vr k r (!b)) = (-1 : ℂ) • ((cM _)ᵀ * cM _ : Matrix _ _ ℂ) := by
  cases b
  · refine Eq.trans ?_ (casimir_kronecker_sum _).1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).1 (hS k r _).2
  · refine Eq.trans ?_ (casimir_kronecker_sum _).2
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).2 (hS k r _).1

def uM (ι : Type) [DecidableEq ι] : Matrix (Unit × ι) ι ℂ := fun p d => if p.2 = d then 1 else 0

theorem uM_int (F : FRep k r) (g : Mx k r) : uM F.ι * F.ρ g = ((triv k r).tens F).ρ g * uM F.ι := by
  ext ⟨_, c⟩ d
  simp [Matrix.mul_apply, uM, Fintype.sum_prod_type]

theorem multOne_of (hC : HomCat) (hM : MatHom) (hT : TensHom) (hL : HomLie) (hS : CasSplit) (hD : StdD)
    (hK : KerZero) (o1 : OKTriv) (o2 : OKVr) (o3 : OKTens) : MultOne := by
  intro k r b B T S Bt cB cT ct hR hB hTc hBt hne hinj hEnd hDS ⟨κ, hκ, hκ0⟩
  have C := hC k r
  let Φ : (M (one T) →ₗ[ℂ] M (vr k r b, B)) → (M (one B) →ₗ[ℂ] M ((vr k r b).tens (vr k r (!b)), B)) :=
    fun i => on1 i ∘ₗ (mAct (uM _) ∘ₗ κ)
  have Φap : ∀ i v c d, Φ i v (c, d) = i (fun _ => κ v d) c := by
    intro i v c d
    simp only [Φ, on1, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
    refine congrFun (congrArg i (funext fun u => ?_)) c
    simp [LinearMap.funLeft_apply, mAct_apply, uM]
  have Φhom : ∀ i, IsHom (one T) (vr k r b, B) i → IsHom (one B) ((vr k r b).tens (vr k r (!b)), B) (Φ i) := by
    intro i hi
    exact C.comp _ ((triv k r).tens (vr k r (!b)), T) _ _ _
      (C.comp _ (vr k r (!b), T) _ _ _ hκ (hM k r _ _ T _ fun g _ => uM_int _ g))
      (hT k r _ _ (vr k r (!b)) _ _ i hi).1
  have chom : IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) :=
    cM_hom hM b B
  have core : ∀ i, IsHom (one T) (vr k r b, B) i → (∀ v, mAct (cM _) (Φ i v) = 0) → i = 0 := by
    intro i hi h0
    have hz : ∀ v c, (fun d => Φ i v (c, d)) = 0 := by
      intro v c
      have e1 := hom_cas hL (o1 k r) (o3 k r _ _ (o2 k r b) (o2 k r (!b))) (Φhom i hi) v
      rw [hB, hS k r _ _ B (o2 k r b) (o2 k r (!b)), hR, qMat_vr hD, mAct_smul, mAct_mul] at e1
      have e2 : cas1 (vr k r b) (vr k r (!b)) B (Φ i v) = cT • Φ i v := by
        funext ⟨c, d⟩
        have := hom_cas hL (o1 k r) (o2 k r b) hi (fun _ => κ v d)
        rw [hTc] at this
        simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul] at this
        show cas (vr k r b, B) (fun c' => Φ i v (c', d)) c = cT • Φ i v (c, d)
        simp only [Φap]
        exact (congrFun this c).symm
      have e3 : cas2 (vr k r b) (vr k r (!b)) B (Φ i v) = (2 * cB - cT) • Φ i v := by
        simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.comp_apply, h0, map_zero, smul_zero, add_zero, e2] at e1
        rw [sub_smul, two_mul, add_smul]
        rw [eq_sub_iff_add_eq] at e1
        rw [e1]; abel
      have e4 : cas (vr k r (!b), B) (fun d => Φ i v (c, d)) = (2 * cB - cT) • fun d => Φ i v (c, d) :=
        funext fun d => congrFun e3 (c, d)
      refine hinj _ fun t p hp => ?_
      have e5 := hom_cas hL (o2 k r (!b)) (o1 k r) hp (fun d => Φ i v (c, d))
      rw [e4, hBt, map_smul, LinearMap.smul_apply, LinearMap.id_apply, ← sub_eq_zero, ← sub_smul] at e5
      exact (smul_eq_zero.1 e5).resolve_left (sub_ne_zero.2 (hne t).symm)
    obtain ⟨v, hv⟩ : ∃ v, κ v ≠ 0 := by
      by_contra hn
      exact hκ0 (LinearMap.ext fun v => not_not.1 fun h => hn ⟨v, h⟩)
    obtain ⟨d, hd⟩ := Function.ne_iff.1 hv
    refine hK k r T _ i hDS hi (fun _ => κ v d) (fun h => hd (congrFun h ())) (funext fun c => ?_)
    rw [← Φap]
    exact congrFun (hz v c) d
  intro i i' hi hi'
  obtain ⟨l, hl⟩ := hEnd _ (C.comp _ _ _ _ _ (Φhom i hi) chom)
  obtain ⟨l', hl'⟩ := hEnd _ (C.comp _ _ _ _ _ (Φhom i' hi') chom)
  obtain ⟨α, β, hab, h0⟩ : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ α * l + β * l' = 0 := by
    by_cases h : l = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h]⟩
    · exact ⟨l', -l, Or.inr (neg_ne_zero.2 h), by ring⟩
  refine ⟨α, β, hab, core _ (C.add _ _ _ _ (C.smul _ _ α _ hi) (C.smul _ _ β _ hi')) fun v => ?_⟩
  have e : Φ (α • i + β • i') v = α • Φ i v + β • Φ i' v := by
    funext ⟨c, d⟩
    simp [Φap]
  have a1 := LinearMap.congr_fun hl v
  have a2 := LinearMap.congr_fun hl' v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at a1 a2
  rw [e, map_add, map_smul, map_smul, a1, a2, smul_smul, smul_smul, ← add_smul, h0, zero_smul]

end CompanionTheory.Zuck

end
