import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetGen

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_gen_of_basis {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module B L'] {g : ℕ}
    (e : Module.Basis (Fin g) R L) (e' : Module.Basis (Fin g) B L') (φ : L →ₛₗ[algebraMap R B] L') (hφ : ∀ j, φ (e j) = e' j)
    (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧ ∀ v, δ' (fun j ↦ φ (v j)) = algebraMap R B (δ v) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hδ ▸ Submodule.mem_top : e.det ∈ Submodule.span R {δ})
  have h1 : c * δ e = 1 := by
    have := congrArg (fun f : L [⋀^Fin g]→ₗ[R] R ↦ f e) hc
    simpa [Module.Basis.det_self] using this
  refine ⟨algebraMap R B (δ e) • e'.det, eq_top_iff.2 fun ω _ ↦ Submodule.mem_span_singleton.2
    ⟨ω e' * algebraMap R B c, ?_⟩, fun v ↦ ?_⟩
  · rw [smul_smul, _root_.mul_assoc, ← map_mul, h1, map_one, _root_.mul_one, ← ω.eq_smul_basis_det e']
  · have hr : ∀ (x : L) (i : Fin g), e'.repr (φ x) i = algebraMap R B (e.repr x i) := fun x i ↦ by
      have : φ x = ∑ j, algebraMap R B (e.repr x j) • e' j := by
        conv_lhs => rw [← e.sum_repr x, map_sum]
        simp only [LinearMap.map_smulₛₗ, hφ]
      rw [this, e'.repr_sum_self]
    have hm : e'.toMatrix (fun j ↦ φ (v j)) = (algebraMap R B).mapMatrix (e.toMatrix v) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hr]
    conv_rhs => rw [δ.eq_smul_basis_det e]
    simp only [AlternatingMap.smul_apply, smul_eq_mul, map_mul, Module.Basis.det_apply, hm, RingHom.map_det]

theorem exists_gen_quot {H H' L L' : Type*} [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module B H'] [AddCommGroup L]
    [Module R L] [AddCommGroup L'] [Module B L'] {K I : Type*} [Fintype K] [Fintype I] {g : ℕ}
    (b : Module.Basis K R H) (b' : Module.Basis K B H') (bc : H →ₛₗ[algebraMap R B] H') (hb : ∀ k, bc (b k) = b' k)
    (t : I → B) (N : I → Module.End R H) (hN : ∀ i j, N i * N j = 0) (q : H →ₗ[R] L) (hq : Function.Surjective q)
    (q' : H' →ₗ[B] L') (hq' : Function.Surjective q')
    (hker : LinearMap.ker q' = Submodule.span B {d | ∃ x ∈ LinearMap.ker q, d = bc x + ∑ i, t i • bc (N i x)})
    (e : Module.Basis (Fin g) R L) (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧
      ∀ x : Fin g → H, δ' (fun j ↦ q' (bc (x j) + ∑ i, t i • bc (N i (x j)))) = algebraMap R B (δ fun j ↦ q (x j)) := by
  have hNN : ∀ i j x, N i (N j x) = 0 := fun i j x ↦ LinearMap.congr_fun (hN i j) x
  let nn : H →ₛₗ[algebraMap R B] H' :=
    { toFun x := bc x + ∑ i, t i • bc (N i x)
      map_add' x y := by
        simp only [map_add, smul_add, Finset.sum_add_distrib]; abel
      map_smul' r x := by
        simp only [map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum, smul_smul, mul_comm] }
  have nn_def : ∀ x, nn x = bc x + ∑ i, t i • bc (N i x) := fun _ ↦ rfl
  have nnN : ∀ i x, nn (N i x) = bc (N i x) := fun i x ↦ by simp [nn_def, hNN]
  have bc_eq : ∀ x, bc x = nn x - ∑ i, t i • nn (N i x) := fun x ↦ by simp only [nnN, nn_def x, add_sub_cancel_right]
  let φ : L →ₛₗ[algebraMap R B] L' :=
    ((LinearMap.ker q).liftQ (q' ∘ₛₗ nn) fun x hx ↦ by
      change nn x ∈ LinearMap.ker q'
      rw [hker]
      exact Submodule.subset_span ⟨x, hx, rfl⟩) ∘ₛₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hφ : ∀ x, φ (q x) = q' (nn x) := fun x ↦ by
    have : (q.quotKerEquivOfSurjective hq).symm (q x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have ext : ∀ l : H →ₗ[R] R, ∃ l' : H' →ₗ[B] B, ∀ x, l' (bc x) = algebraMap R B (l x) := fun l ↦
    ⟨b'.constr B fun k ↦ algebraMap R B (l (b k)), fun x ↦ by
      have h : ∀ k, (b'.constr B fun k ↦ algebraMap R B (l (b k))) (b' k) = algebraMap R B (l (b k)) :=
        fun k ↦ b'.constr_basis B _ k
      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum]
      conv_rhs => rw [← b.sum_repr x, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [bc.map_smulₛₗ, map_smul, hb, h, map_smul, smul_eq_mul, smul_eq_mul, map_mul]⟩
  have coord : ∀ l : L →ₗ[R] R, ∃ l' : L' →ₗ[B] B, ∀ v, l' (φ v) = algebraMap R B (l v) := fun l ↦ by
    obtain ⟨l₀, h₀⟩ := ext (l ∘ₗ q)
    choose l₁ h₁ using fun i ↦ ext (l ∘ₗ q ∘ₗ N i)
    let ξ : H' →ₗ[B] B := l₀ - ∑ i, t i • l₁ i
    have hξ : ∀ x, ξ (nn x) = algebraMap R B (l (q x)) := fun x ↦ by
      simp [ξ, nn_def, LinearMap.sum_apply, map_sum, h₀, h₁, hNN]
    have hk : LinearMap.ker q' ≤ LinearMap.ker ξ := by
      rw [hker, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      change ξ (nn x) = 0
      rw [hξ, LinearMap.mem_ker.1 hx, map_zero, map_zero]
    refine ⟨(LinearMap.ker q').liftQ ξ hk ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap, fun v ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hq v
    have : (q'.quotKerEquivOfSurjective hq').symm (q' (nn x)) = Submodule.Quotient.mk (nn x) :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply, hξ]
  have li : LinearIndependent B fun j ↦ φ (e j) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨l', hl'⟩ := coord (e.coord j)
    have := congrArg l' hc
    simpa [map_sum, hl', Finsupp.single_apply, apply_ite (algebraMap R B)] using this
  have sp : ⊤ ≤ Submodule.span B (Set.range fun j ↦ φ (e j)) := by
    have h1 : ∀ v, φ v ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun v ↦ by
      rw [← e.sum_repr v, map_sum]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h2 : ∀ x, q' (bc x) ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun x ↦ by
      rw [bc_eq, map_sub, map_sum, ← hφ]
      refine sub_mem (h1 _) (Submodule.sum_mem _ fun i _ ↦ ?_)
      rw [map_smul, ← hφ]
      exact Submodule.smul_mem _ _ (h1 _)
    intro w _
    obtain ⟨d, rfl⟩ := hq' w
    rw [← b'.sum_repr d, map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [map_smul, ← hb]
    exact Submodule.smul_mem _ _ (h2 _)
  obtain ⟨δ', h1, h2⟩ := exists_gen_of_basis e (Module.Basis.mk li sp) φ (fun j ↦ by simp) δ hδ
  refine ⟨δ', h1, fun x ↦ ?_⟩
  rw [← h2]
  simp only [hφ, nn_def]

end Alg

theorem nonempty_basis_lie (H : GlobalTheory.Published.AbelianDeRham.Hodge) {R : Type} [CommRing R] [IsLocalRing R] {A : Over (Sp R)} [GrpObj A]
    [IsCommMonObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {O : Type} [CommRing O]
    (a : OAct O A) : Nonempty (Module.Basis (Fin g) R (Serre.Lie a)) := by
  obtain ⟨hL, ⟨M, hM⟩, h1, h2, h3⟩ := H R A g hA hg
  haveI : Module.Free R (PrimitiveSubmodule A) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R (PrimitiveSubmodule A) = g := by
    have := h3 (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hs : Function.Surjective (PrimitiveSubmodule A).dualRestrict := fun l ↦
    ⟨l ∘ₗ (PrimitiveSubmodule A).projectionOnto M hM, LinearMap.ext fun c ↦ by simp⟩
  let E : (HdR A ⧸ Fil A) ≃ₗ[R] Module.Dual R (PrimitiveSubmodule A) :=
    (Submodule.quotEquivOfEq _ _ (Submodule.dualRestrict_ker_eq_dualAnnihilator _).symm).trans
      ((PrimitiveSubmodule A).dualRestrict.quotKerEquivOfSurjective hs)
  exact ⟨(Module.finBasisOfFinrankEq R _ hr).dualBasis.map (E.symm.trans (hL.quotEquiv a))⟩

theorem main : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC →
    ∀ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} →
      ∃ δ' : X'.DetGen, ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
        (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
        (∀ j, IsJetElt J X N m (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
          δ'.1 v' = algebraMap R J.B (δ.1 v) := by
  intro _ H _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X δ N hN m hm X' i pull hfil
  classical
  obtain ⟨e⟩ := nonempty_basis_lie H.2.1 X.ab X.dim X.rm
  obtain ⟨f1, f2, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  let p := Module.Free.chooseBasis R (primDR X.A)
  let p' := (Algebra.TensorProduct.basis J.B p).map (LinearEquiv.ofBijective _ hm)
  have hp : ∀ k, p' k = m.pull (p k) := fun k ↦ by
    simp only [p', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact (liftSemi_tmul m.pull 1 (p k)).trans (one_smul _ _)
  have hc : ∀ x c, hm.bcMap x (m.pull c) = algebraMap R J.B (x c) := fun x ↦ hm.corr_iff.2 rfl
  have hb : ∀ k, hm.bcMap (p.dualBasis k) = p'.dualBasis k := fun k ↦ p'.ext fun l ↦ by
    rw [Module.Basis.dualBasis_apply_self, hp, hc, Module.Basis.dualBasis_apply_self]
    split_ifs <;> simp
  have hj : ∀ x d, IsJetElt J X N m x d ↔ d = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := fun x d ↦ by
    constructor
    · intro h
      refine p'.ext fun l ↦ ?_
      rw [hp, h]
      simp [LinearMap.sum_apply, hc]
    · rintro rfl c
      simp [LinearMap.sum_apply, hc]
  have hπ : Function.Surjective J.π := fun r ↦ ⟨r • J.b ⟨0, by simp⟩, by simp [J.π_eq]⟩
  have hbij := GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective H.2.2.2.1 X'.ab X'.dim J.nil hπ rfl pull.grp
  have hL := (H.2.1 R X.A _ X.ab X.dim).1
  have hL' := (H.2.1 J.B X'.A _ X'.ab X'.dim).1
  obtain ⟨δ', h1, h2⟩ := exists_gen_quot p.dualBasis p'.dualBasis hm.bcMap hb J.t N hN.2.1 (hL.toLie X.rm)
    (hL.toLie_surjective _) (hL'.toLie X'.rm ∘ₗ crysToDR J.κ pull.grp) ((hL'.toLie_surjective _).comp hbij.2)
    (by
      rw [LinearMap.ker_comp, hL'.ker_toLie, hL.ker_toLie]
      simp only [← hj]
      exact hfil) e δ.1 δ.2
  refine ⟨⟨δ', h1⟩, fun x d v v' h ↦ ?_⟩
  obtain rfl : v = fun j ↦ hL.toLie X.rm (x j) := funext fun j ↦ ((hL.toLie_eq_iff _).2 (h j).2.1).symm
  rw [← h2]
  refine congrArg δ' (funext fun j ↦ ?_)
  rw [← (hj _ _).1 (h j).1]
  exact ((hL'.toLie_eq_iff _).2 (h j).2.2).symm

end GlobalTheory.JetGen
