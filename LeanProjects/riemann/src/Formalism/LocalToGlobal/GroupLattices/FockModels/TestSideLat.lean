import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideTen

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

structure PosCore (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (p m : ℕ) (lam : Fin (m + 1) → ℤ) (N : ℕ)
    (β : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)) ≃ₗ[Kf]
      Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) : Prop where
  up : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit M.det →
    ∀ Q : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      (∀ P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
        (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam M →
          β Q P ∈ Set.range (algebraMap O Kf)) →
      (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam (M⁻¹).transpose
  low : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit M.det →
    ∀ Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam (M⁻¹).transpose →
      (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam M →
        β (((p : Kf) ^ N) • Q) P ∈ Set.range (algebraMap O Kf)

theorem latBasis {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : IsUnit M.det) :
    ∃ Z : Module.Basis ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      Submodule.span O (Set.range fun i => ((Z i : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)) = nablaLTw O Kf m lam M := by
  obtain ⟨B, -, b2, b3, b4⟩ := la_basis hinj m lam M hM
  refine ⟨(Module.Basis.span b3).map (LinearEquiv.ofEq _ _ b4), ?_⟩
  rw [← b2]
  congr 2
  funext i
  show (((LinearEquiv.ofEq _ _ b4) (Module.Basis.span b3 i) : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) = _
  rw [LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Module.Basis.span_apply b3 i)

theorem repr_int {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} (Z : Module.Basis I Kf V) (P : V)
    (hP : P ∈ Submodule.span O (Set.range Z)) (j : I) : Z.repr P j ∈ Set.range (algebraMap O Kf) := by
  classical
  induction hP using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a1, h1⟩ := hu
    obtain ⟨a2, h2⟩ := hv
    exact ⟨a1 + a2, by rw [map_add, map_add, Finsupp.add_apply, h1, h2]⟩
  | smul c v _ hv =>
    obtain ⟨a1, h1⟩ := hv
    refine ⟨c * a1, ?_⟩
    rw [← algebraMap_smul Kf c v, map_smul, Finsupp.smul_apply, map_mul, h1, smul_eq_mul]

theorem li_coe {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (hinj : Function.Injective (algebraMap O Kf)) {I : Type}
    (Vs : Submodule Kf X) (Z : Module.Basis I Kf Vs) : LinearIndependent O (fun i => ((Z i : Vs) : X)) := by
  have h1 : LinearIndependent Kf (fun i => ((Z i : Vs) : X)) :=
    Z.linearIndependent.map' Vs.subtype (Submodule.ker_subtype _)
  exact h1.restrict_scalars (by
    intro a b hab
    apply hinj
    simpa [Algebra.smul_def] using hab)

theorem ten_side (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    (p : ℕ) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (N : Fin n' → ℕ)
    (β : ∀ s : Fin n', ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) ≃ₗ[Kf]
      Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))))
    (hβ : ∀ s, PosCore O Kf p m (lamAt lam0 s) (N s) (β s))
    (Vs : Submodule Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    (hVs : Vs = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) :
    ∃ Ψ : Module.Dual Kf Vs ≃ₗ[Kf] Vs,
      ∀ Ms : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ms s).det) →
        (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) ≤
          (Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O) ∧
        scale ((p : Kf) ^ (∑ s, N s))
            ((Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O)) ≤
          (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) := by
  subst hVs
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hfin : ∀ s : Fin n', Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).to_subtype
  let _ : ∀ s : Fin n', Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  set V : Fin n' → Submodule Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
    fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) with hV
  have hb := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) 1 (by simp)
  choose b _ using hb
  obtain ⟨Ψ, hΨ⟩ := psi_exists V β b
  refine ⟨Ψ, fun Ms hMs => ?_⟩
  have hMs' : ∀ s, IsUnit (((Ms s)⁻¹).transpose).det := fun s => det_invT _ (hMs s)
  have hZ := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) (Ms s) (hMs s)
  choose Z hZ using hZ
  obtain ⟨z, hz⟩ := prodBasis V Z
  obtain ⟨z', hz'⟩ := prodBasis V (fun s => dualB (β s) (Z s))
  have hH : ∀ Ns : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ns s).det) →
      Hten O lam0 (fun s => colSpan O (Ns s)) =
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) (Ns s)) := by
    intro Ns hNs
    unfold Hten
    congr 1
    funext s
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (hNs s)]

  have hΛ : (Hten O lam0 fun s => colSpan O (Ms s)).comap ((tensorLat Kf Kf V).subtype.restrictScalars O) =
      Submodule.span O (Set.range z) := by
    obtain ⟨-, oS⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ _
      (fun s i => ((Z s i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (Z s)) hZ
    rw [hH Ms hMs, ← oS, ← comap_span_coe]
    congr 3
    funext i
    exact (hz i).symm
  have hdual : dualLat O Kf (Submodule.span O (Set.range z)) =
      Submodule.span O (Set.range fun i => z.coord i) := by
    have := dualLat_span (O := O) z (fun _ => 1) (fun _ => one_ne_zero)
    simpa using this
  have hmap : (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap
      ((tensorLat Kf Kf V).subtype.restrictScalars O))).map (Ψ.toLinearMap.restrictScalars O) =
      Submodule.span O (Set.range z') := by
    rw [hΛ, hdual, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hΨ Z z z' hz hz' j
  rw [hmap]
  have hPmem : ∀ s (P : V s), (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈
      nablaLTw O Kf m (lamAt lam0 s) (Ms s) → P ∈ Submodule.span O (Set.range (Z s)) := by
    intro s P hP
    rw [← hZ s] at hP
    rw [← comap_span_coe]
    exact hP
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ((z' j : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose
    rw [hz', hH _ hMs']
    apply Submodule.subset_span
    refine ⟨fun s => ((dualB (β s) (Z s) (j s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
      fun s => ?_, rfl⟩
    apply (hβ s).up (Ms s) (hMs s)
    intro P hP
    rw [beta_dualB, Module.Basis.coord_apply]
    exact repr_int (Z s) P (hPmem s P hP) (j s)
  · rintro _ ⟨Q, hQ, rfl⟩
    show ((p : Kf) ^ (∑ s, N s)) • Q ∈ Submodule.span O (Set.range z')
    rw [← comap_span_coe]
    show ((((p : Kf) ^ (∑ s, N s)) • Q : tensorLat Kf Kf V) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Submodule.span O (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    obtain ⟨-, oS'⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun i =>
        ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)))
      (fun s i => ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (dualB (β s) (Z s))) (fun s => rfl)
    have hr : (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
        Set.range fun i : (∀ s, ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) =>
          ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := by
      congr 1
      funext i
      exact hz' i
    rw [hr, oS', Submodule.coe_smul, ← Finset.prod_pow_eq_pow_sum]
    have hQ' : (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) ((Ms s)⁻¹).transpose) := by
      rw [← hH _ hMs']
      exact hQ
    refine lb_tensor O Kf _ _ (fun s => (p : Kf) ^ N s) (fun s F hF => ?_) _ hQ'
    have hFV : F ∈ V s := la_nablaLTw_le m (lamAt lam0 s) _ (hMs' s) F hF
    have h1 : (((p : Kf) ^ N s) • (⟨F, hFV⟩ : V s)) ∈
        Submodule.span O (Set.range fun i => (1 : Kf) • dualB (β s) (Z s) i) := by
      apply mem_span_of_coord (dualB (β s) (Z s)) (fun _ => 1) (fun _ => one_ne_zero)
      intro i
      rw [inv_one, one_mul, Module.Basis.coord_apply, dualB_repr]
      apply (hβ s).low (Ms s) (hMs s) ⟨F, hFV⟩ (Z s i) hF
      rw [← hZ s]
      exact Submodule.subset_span ⟨i, rfl⟩
    simp only [one_smul] at h1
    rw [← comap_span_coe] at h1
    exact h1

end Formalism.L2.G.Model
