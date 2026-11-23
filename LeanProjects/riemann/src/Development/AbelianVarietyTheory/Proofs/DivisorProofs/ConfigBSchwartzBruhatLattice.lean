import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionAdapted
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

open scoped GlobalTheory.VacAny
open Topology

noncomputable section

namespace GlobalTheory.ShiftLocConst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_add_of_symp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  linear_combination (-⅟(2 : R)) * h + (a.1 ⬝ᵥ b.2) * h2

omit [NumberField E] in

theorem exists_locLin {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (g : AE F E →ₗ[AF F] V) :
    ∃ T : Fv F v ⊗[F] E →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v),
      ∀ z, T (compFin F E v z) = GlobalTheory.LatVac.locCo co v (g z) := by
  have hs : ∀ (a : AF F) (w : V), GlobalTheory.LatVac.locCo co v (a • w) = evFin F v a • GlobalTheory.LatVac.locCo co v w := fun a w => by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> simp [GlobalTheory.LatVac.locCo]
  let f : E →ₗ[F] (κ → Fv F v) × (κ → Fv F v) :=
    { toFun := fun x => GlobalTheory.LatVac.locCo co v (g ((1 : AF F) ⊗ₜ[F] x))
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add, map_add]
      map_smul' := fun c x => by
        rw [TensorProduct.tmul_smul, ← algebraMap_smul (AF F) c, map_smul, hs, RingHom.id_apply,
          ← algebraMap_smul (Fv F v) c]
        rfl }
  refine ⟨f.liftBaseChange (Fv F v), fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    have e' : a ⊗ₜ[F] x = a • ((1 : AF F) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, LinearMap.liftBaseChange_tmul, e', map_smul, hs]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [NumberField E] in

theorem compFin_surjective (v : Pl F) : Function.Surjective (compFin F E v) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    refine ⟨GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x, ?_⟩
    conv_rhs => rw [← GlobalTheory.LatVac.evFin_liftV v a]
    rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

omit [NumberField E] in

theorem exists_open_of_isotropic {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (g : AE F E →ₗ[AF F] V) (hg : ∀ a b, Bf (g a) (g b) = 0) {ψ : AddChar (Fv F v) ℂ}
    (hψ : Continuous ψ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    ∃ Λ : AddSubgroup (Fv F v ⊗[F] E), IsOpen (Λ : Set (Fv F v ⊗[F] E)) ∧
      ∀ l l' : AE F E, compFin F E v l' - compFin F E v l ∈ Λ →
        schr ψ (GlobalTheory.LatVac.locCo co v (g l')) φ = schr ψ (GlobalTheory.LatVac.locCo co v (g l)) φ := by
  obtain ⟨T, hT⟩ := exists_locLin co v g
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have hadd : ∀ z z', schr ψ (T (z + z')) φ = schr ψ (T z) (schr ψ (T z') φ) := fun z z' => by
    rw [map_add]
    refine schr_add_of_symp ψ _ _ ?_ φ
    obtain ⟨a, rfl⟩ := compFin_surjective v z
    obtain ⟨b, rfl⟩ := compFin_surjective v z'
    have h := congrArg (evFin F v) ((co.form (g a) (g b)).symm.trans (hg a b))
    rw [hT, hT]
    simpa [GlobalTheory.LatVac.locCo, dotProduct] using h
  have h0 : schr ψ (T 0) φ = φ := by
    funext x
    simp [schr]
  let Λ : AddSubgroup (Fv F v ⊗[F] E) :=
    { carrier := {z | schr ψ (T z) φ = φ}
      zero_mem' := h0
      add_mem' := fun {z z'} hz hz' => by
        change schr ψ (T (z + z')) φ = φ
        rw [hadd, show schr ψ (T z') φ = φ from hz', show schr ψ (T z) φ = φ from hz]
      neg_mem' := fun {z} hz => by
        have h := hadd (-z) z
        rw [neg_add_cancel, h0, show schr ψ (T z) φ = φ from hz] at h
        exact h.symm }
  refine ⟨Λ, AddSubgroup.isOpen_of_mem_nhds (g := 0) Λ ?_, fun l l' h => ?_⟩
  · have hc : Tendsto T (𝓝 0) (𝓝 0) := by
      simpa using (IsModuleTopology.continuous_of_linearMap T).tendsto 0
    exact hc.eventually (GlobalTheory.VacAvg.eventually_schr_fix v ψ hψ hφ)
  · have h1 := hadd (compFin F E v l) (compFin F E v l' - compFin F E v l)
    rw [add_sub_cancel, show schr ψ (T (compFin F E v l' - compFin F E v l)) φ = φ from h, hT, hT] at h1
    exact h1

theorem shiftB_locConst : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ Λ : AddSubgroup (Fv F B.v₁ ⊗[F] E), IsOpen (Λ : Set (Fv F B.v₁ ⊗[F] E)) ∧
      ∀ l l' : (AE F E)ˣ, compFin F E B.v₁ l'.1 - compFin F E B.v₁ l.1 ∈ Λ →
        locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l'))) φ = locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT φ hφ
  have hψ : Continuous B.ψ := hT.base.std.1
  let g : AE F E →ₗ[AF F] Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E) :=
    { toFun := fun z => cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x)
      map_add' := fun x y => by rw [map_add, add_smul]
      map_smul' := fun c x => by rw [map_smul, smul_assoc, RingHom.id_apply] }
  have hg : ∀ z, g z = Matrix.vecMulVec (incV F H.y) (cA σ z • incV F H'.x) := fun z =>
    (Matrix.vecMulVec_smul _ _ _).symm
  obtain ⟨Λ, hΛ, h⟩ := exists_open_of_isotropic G.M'.co B.v₁ g
    (fun x y => by
      rw [hg, hg]
      exact GlobalTheory.VacResNonvan.symp_vecMulVec_self_eq_zero F E σ _ _ _ H.y hC.hH.yy _ _)
    (GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ B.v₁) hφ
  refine ⟨Λ, hΛ, fun l l' hl => ?_⟩
  rw [(locOp_rho G.M'.co hψ B.v₁ _ hφ).2, (locOp_rho G.M'.co hψ B.v₁ _ hφ).2]
  exact h l.1 l'.1 hl

end GlobalTheory.ShiftLocConst

end
