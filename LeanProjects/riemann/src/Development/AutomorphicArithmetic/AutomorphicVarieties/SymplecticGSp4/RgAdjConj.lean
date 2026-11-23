import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MemOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TbTriDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix TensorProduct

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem rg_twist {Γ k V : Type} [Group Γ] [CommRing k] [AddCommGroup V] [Module k V] (A : Representation k Γ V)
    (p : V →ₗ[k] V) (hp : ∀ x, p (p x) = p x) (hA : ∀ g x, p (A g x) = A g (p x)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ V, ∀ g x, ρ g x = A g (p x) + (η g : k) • A g (x - p x) := by
  refine ⟨{ toFun := fun g => A g ∘ₗ p + (η g : k) • (A g ∘ₗ (LinearMap.id - p))
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun g x => rfl⟩
  · ext x
    simp
  · ext x
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Module.End.mul_apply, map_add, map_smul, map_sub, hA, hp, sub_self, smul_zero, add_zero,
      mul_smul, smul_sub, smul_add, map_zero]
    module

private theorem rg_sign {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] (k : Type) [Field k] :
    ∃ η : G ℚ Ω →* kˣ, (∀ s : G K Ω, η (s.restrictScalars ℚ) = 1) ∧
      ∀ c : G ℚ Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → η c = -1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : K, IsCMField.complexConj K x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one K (AlgEquiv.ext hc)
  set δ : K := x - IsCMField.complexConj K x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hx.symm
  have hδc : IsCMField.complexConj K δ = -δ := by simp [hδ]
  have hsq : δ * δ ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 (by rw [map_mul, hδc]; ring)
  obtain ⟨q, hq⟩ := Af.surjective_algebraMap_real K h ⟨_, hsq⟩
  have hq' : algebraMap ℚ K q = δ * δ := by
    have := congrArg (fun y : maximalRealSubfield K => (y : K)) hq
    simpa using this
  set d : Ω := algebraMap K Ω δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ0
  have hdd : d * d = algebraMap ℚ Ω q := by rw [IsScalarTower.algebraMap_apply ℚ K Ω, hq', map_mul]
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hne : -d ≠ d := fun e => hd0 (by linear_combination (-1 / 2 : Ω) * e)
  have hpm : ∀ g : G ℚ Ω, g d = d ∨ g d = -d := fun g => by
    have : g d * g d = d * d := by rw [← map_mul, hdd, AlgEquiv.commutes]
    exact mul_self_eq_mul_self_iff.1 this
  refine ⟨{ toFun := fun g => if g d = d then 1 else -1
            map_one' := by simp
            map_mul' := fun g g' => ?_ }, fun s => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · rcases hpm g with h1 | h1 <;> rcases hpm g' with h2 | h2 <;> simp [AlgEquiv.mul_apply, h1, h2, hne]
  · have : (s.restrictScalars ℚ) d = d := s.commutes δ
    simp [this]
  · have : c d = -d := by
      apply j.injective
      rw [hj, hd, ← map_neg (algebraMap K Ω), ← hδc]
      exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) δ).symm
    simp [this, hne]

section BK

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

private theorem rg_bk {ρ ρ' : Representation C (G F Ω) V} (f : V →ₗ[C] V) (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    {z : G F Ω → V} (hz : ∀ g, f (z g) = z g) (h1 : z ∈ Z1 ρ) (h2 : Af.IsBK l ρ z) : z ∈ Z1 ρ' ∧ Af.IsBK l ρ' z := by
  have hc : ∀ g h, z (g * h) = z g + ρ' g (z h) := fun g h => by
    rw [← hz (g * h), h1.2, map_add, hf, hz, hz]
  refine ⟨⟨h1.1, hc⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [← hz, hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc1, -⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hc1, fun g h => hc g.1.1 h.1.1⟩,
      LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
        (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
        Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
          (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Loc.actC, hf]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    simp [hz]

end BK

private def rgJ (k : Type) [CommRing k] : GL (Fin 4) k where
  val := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  inv := !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem rgJ_adj {k : Type} [CommRing k] (X : M4 k) : Xᵀ * (rgJ k : M4 k) = (rgJ k : M4 k) * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

private noncomputable def rgP (k : Type) [Field k] : M4 k →ₗ[k] M4 k where
  toFun X := (2 : k)⁻¹ • (X - adj X)
  map_add' X Y := by rw [(grp k).2.2.1, ← smul_add]; congr 1; abel
  map_smul' a X := by rw [(grp k).2.2.2.1, ← smul_sub, smul_comm]; rfl

private theorem rgP_apply {k : Type} [Field k] (X : M4 k) : rgP k X = (2 : k)⁻¹ • (X - adj X) := rfl

private theorem rgP_mem {k : Type} [Field k] (X : M4 k) : rgP k X ∈ sp4 k := by
  have h1 : adj (-adj X) = -X := by
    rw [← neg_one_smul k, (grp k).2.2.2.1, (grp k).2.1, neg_one_smul]
  show adj _ = -_
  rw [rgP_apply, (grp k).2.2.2.1, sub_eq_add_neg, (grp k).2.2.1, h1, ← smul_neg]
  congr 1
  abel

private theorem rgP_of_mem {k : Type} [Field k] [CharZero k] {X : M4 k} (h : X ∈ sp4 k) : rgP k X = X := by
  have h' : adj X = -X := h
  rw [rgP_apply, h', sub_neg_eq_add, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

private theorem rg_adjConj {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (g : Γ) (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  have h1 : adj (r g) = (θ g : k) • r g⁻¹ := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g) (by rw [← map_mul]; simp)
  have h2 : adj (r g⁻¹) = (θ g⁻¹ : k) • r g := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g⁻¹) (by rw [← map_mul]; simp)
  rw [(grp k).1, (grp k).1, h1, h2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul]
  simp

private theorem rg_ad {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (g : Γ) (X : M4 k) :
    Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := rfl

private theorem rg_pair {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (c s s' : Γ) (hs : s' = c * s * c⁻¹) :
    (r.toHomUnits s : M4 k)ᵀ * (rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) * (r.toHomUnits s' : M4 k) =
      (θ s : k) • ((rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) : M4 k) := by
  show (r s)ᵀ * ((rgJ k : M4 k) * r c⁻¹) * r s' = (θ s : k) • ((rgJ k : M4 k) * r c⁻¹)
  have h := hm s
  unfold IsGSp at h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by
    rw [← map_mul, ← map_mul, hs]
    congr 1
    group
  rw [mul_assoc, mul_assoc, e, ← mul_assoc, rgJ_adj, mul_assoc, ← mul_assoc (adj _), h, smul_mul_assoc, one_mul, mul_smul_comm]

private theorem rg_alg {Γ k : Type} [Group Γ] [Field k] [CharZero k] (r : Γ →* M4 k) (θ : Γ →* kˣ)
    (hm : ∀ g, IsGSp (θ g : k) (r g)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ (M4 k),
      (∀ g X, η g = 1 → ρ g X = (r.toHomUnits g : M4 k) * X * ((r.toHomUnits g)⁻¹ : GL (Fin 4) k)) ∧
      (∀ g X, η g = -1 → ρ g X = -((((rgJ k * (r.toHomUnits g)⁻¹)⁻¹ : GL (Fin 4) k) : M4 k) * Xᵀ *
        (rgJ k * (r.toHomUnits g)⁻¹ : GL (Fin 4) k))) ∧
      (∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = ρ g (rgP k X)) ∧
      ∀ g X Z, Z * r g⁻¹ ∈ sp4 k → Z * r g⁻¹ = ρ g X - X → Z = -rgP k X * r g - r g * -rgP k X := by
  have hpp : ∀ X, rgP k (rgP k X) = rgP k X := fun X => rgP_of_mem (rgP_mem X)
  have hpA : ∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = Loc.adGL r.toHomUnits g (rgP k X) := fun g X => by
    rw [rgP_apply, rgP_apply, map_smul, map_sub, rg_ad, rg_ad, rg_adjConj r θ hm]
  obtain ⟨ρ, hρ⟩ := rg_twist (Loc.adGL r.toHomUnits) (rgP k) hpp hpA η
  refine ⟨ρ, fun g X h => ?_, fun g X h => ?_, fun g X => ?_, fun g X Z h1 h2 => ?_⟩
  · rw [hρ, h, Units.val_one, one_smul, ← map_add, add_sub_cancel]
    rfl
  · rw [mul_inv_rev, inv_inv]
    show _ = -((r g * ((rgJ k)⁻¹ : GL _ _)) * Xᵀ * ((rgJ k : M4 k) * r g⁻¹))
    have e : rgP k X - (X - rgP k X) = -adj X := by
      rw [rgP_apply]
      match_scalars <;> field_simp <;> ring
    rw [hρ, h, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, e, map_neg, rg_ad,
      mul_assoc _ Xᵀ, ← mul_assoc Xᵀ, rgJ_adj]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · rw [hρ, hpp, sub_self, map_zero, smul_zero, add_zero, hpA]
  · have e1 : Z * r g⁻¹ = r g * rgP k X * r g⁻¹ - rgP k X := by
      rw [← rgP_of_mem h1, h2, map_sub, hρ, map_add, map_smul, hpA, hpA, map_sub, hpp, sub_self, map_zero, smul_zero,
        add_zero, rg_ad]
    have := congrArg (· * r g) e1
    simp only [sub_mul, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    rw [this]
    noncomm_ring

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.rigid :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → Af.AdVanishQ → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ ι r, D.EPt r → Irr r → Aut.IsAut4 ι r → D.RigidAt r := by
  intro Ω _ _ _ l _ c D hD hP hAd N hN h1 h2 h3 ι r hr hirr haut r' hr' hfst
  obtain ⟨hlev, θ, hθ, hdual, hθv⟩ := level D hD N hN h1 h2 h3 r hr
  obtain ⟨K, _, _, _, _, _, _, hK, hirrK⟩ := irrK D hD r hr hirr
  obtain ⟨hz, hbk, hsp⟩ := tanBK D hD hP r hr r' hr' hfst
  have hm : ∀ g, IsGSp (θ g : PadicAlgCl l) (r g) := fun g => by
    rw [hθv]
    exact (ptIn D hD _ r hr).1 g
  obtain ⟨η, hη1, hη2⟩ := rg_sign (Ω := Ω) hK (PadicAlgCl l)
  obtain ⟨ρ, ha, hb, hf, hd⟩ := rg_alg r θ hm η
  have hcc : ∃ j : Ω →+* ℂ, ∀ x, j (D.cc x) = starRingEnd ℂ (j x) := hD.isCC
  have had : Af.IsAdOf (r.toHomUnits.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))
      (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) ρ :=
    ⟨D.cc, rgJ _ * (r.toHomUnits D.cc)⁻¹, hcc, fun s s' hs => rg_pair r θ hm D.cc _ _ hs, fun s X => ha _ X (hη1 s),
      fun X => hb _ X (hη2 _ hcc)⟩
  have hv := hAd K hK 4 (by norm_num) l Ω ι r.toHomUnits _ θ hlev.cont haut hθ hdual hirrK ρ had
  obtain ⟨hz', hbk'⟩ := rg_bk (rgP _) hf (fun g => rgP_of_mem (hsp g)) hz hbk
  obtain ⟨X, hX⟩ := (mem_coboundaries1 _ _).1 (hv _ hz' hbk')
  exact ⟨-rgP (PadicAlgCl l) X, (sp4 (PadicAlgCl l)).neg_mem (rgP_mem (k := PadicAlgCl l) X), fun g i j => congrFun (congrFun (hd g X _ (hsp g) (hX g)) i) j⟩
