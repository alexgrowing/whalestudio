import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmDOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.Per GlobalTheory.AdmBr

namespace GlobalTheory.CrysSubRep

variable {l : ℕ} [Fact l.Prime]

def entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) : FinExt l :=
  ⟨L.1 ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2),
    haveI := L.2
    haveI : FiniteDimensional ℚ_[l]
        (IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    IntermediateField.finiteDimensional_sup _ _⟩

theorem le_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) :
    L.1 ≤ (entExt L M).1 := le_sup_left

theorem mem_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) (i : Fin d) (j : Fin a) :
    M i j ∈ (entExt L M).1 :=
  (le_sup_right : IntermediateField.adjoin ℚ_[l] _ ≤ (entExt L M).1)
    (IntermediateField.subset_adjoin _ _ ⟨(i, j), rfl⟩)

theorem exists_leftInv {K : Type} [Field K] {d a : ℕ} (M : Matrix (Fin d) (Fin a) K)
    (h : Function.Injective M.mulVec) : ∃ N : Matrix (Fin a) (Fin d) K, N * M = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M)
    (LinearMap.ker_eq_bot.2 (by rw [Matrix.toLin'_apply', Matrix.coe_mulVecLin]; exact h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem exists_model_of_mem {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Formalism.MainNotions.N.mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, MonoidHom.ext fun g => Units.ext (hM g)⟩

end GlobalTheory.CrysSubRep

namespace GlobalTheory.CrysSubRep

theorem isCrysAt_of_sub : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (d a : ℕ) (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℚ_[l])
    (r : ↥Gw →* GL (Fin a) (Om l)),
    IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin d → ℚ_[l])) →
    ∀ M : Matrix (Fin d) (Fin a) (Om l), Function.Injective M.mulVec →
    (∀ g : ↥Gw, ((ρ (Bw.e g) : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) * M =
      M * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
    GlobalTheory.Pst.IsCrysAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw d a ρ r hρ M hM hint
  obtain ⟨T⟩ := hT
  let L : FinExt l := entExt Bw.LL M
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M' : Matrix (Fin d) (Fin a) ↥L.1 := Matrix.of fun i j => ⟨M i j, mem_entExt Bw.LL M i j⟩
  have hM' : M'.map f = M := Matrix.ext fun i j => rfl
  have hinjM' : Function.Injective M'.mulVec := by
    intro x y hxy
    have h1 : ∀ v : Fin a → ↥L.1, M.mulVec (fun i => f (v i)) = fun i => f (M'.mulVec v i) :=
      fun v => funext fun i => by rw [← hM']; exact (RingHom.map_mulVec f M' v i).symm
    have h2 := hM (show M.mulVec (fun i => f (x i)) = M.mulVec (fun i => f (y i)) by rw [h1, h1, hxy])
    exact funext fun i => f.injective (congrFun h2 i)
  obtain ⟨N, hN⟩ := exists_leftInv M' hinjM'
  let ρL : ↥(GK Bw.Kw) →* Matrix (Fin d) (Fin d) ↥L.1 :=
    (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hmapρ : ∀ g, ((ρ g : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) =
      (ρL g).map f := fun g => by
    simp only [ρL, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Units.coeHom_apply, Matrix.map_map]
    congr 1
  have hint' : ∀ g, (ρL (Bw.e g)).map f * M'.map f = M'.map f * (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hmapρ, hM']; exact hint g
  have hr : ∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)) = (N * ρL (Bw.e g) * M').map f := fun g => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, hint', ← Matrix.mul_assoc, ← Matrix.map_mul, hN,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mul]
  have hmem : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [hr g]; exact ((N * ρL (Bw.e g) * M') i j).2
  obtain ⟨r', hr'⟩ := exists_model_of_mem r L hmem
  have hmod : GlobalTheory.Pst.IsModel Bw r L r' := ⟨le_entExt Bw.LL M, hr'⟩
  have hr'g : ∀ g, ((r' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map f =
      (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hr']; rfl
  have hinjMap : ∀ {m n : ℕ}, Function.Injective (fun X : Matrix (Fin m) (Fin n) ↥L.1 => X.map f) :=
    fun {m n} X Y h => Matrix.ext fun i j => f.injective (congrFun (congrFun h i) j)
  have hintL : ∀ g, ρL (Bw.e g) * M' = M' * (r' g : Matrix (Fin a) (Fin a) ↥L.1) := fun g =>
    hinjMap (by simp only [Matrix.map_mul]; rw [hr'g]; exact hint' g)
  haveI := L.2
  have hcL : IsCrys (P.PD Bw.Kw) (Formalism.MainNotions.N.matRep ρL) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin d) (Fin d) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).2 hρ
  refine ⟨L, r', hmod, ?_⟩
  refine GlobalTheory.TateDualCrys.isCrys_of_isSubOfSums T Bw.Kw L (ι := Unit) (fun _ => ρL) (fun _ => hcL) (Fin a → ↥L.1)
    (Bw.repE L r') ⟨1, fun _ => (), LinearMap.pi (fun _ => Matrix.toLin' M'), fun x y h => hinjM' (congrFun h 0), ?_⟩
  intro g v
  funext i
  have e1 := hintL (Bw.e.symm g)
  rw [MulEquiv.apply_symm_apply] at e1
  show M'.mulVec ((r' (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1).mulVec v) = (ρL g).mulVec (M'.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]

end GlobalTheory.CrysSubRep
