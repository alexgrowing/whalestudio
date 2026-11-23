import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActExtLApply
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleLatticeMatrixOfPeriodData
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmulSurjectiveRankOne
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem twisted_matrix_mulVec_base_change {G O LL : Type} [Group G] [CommRing O] [Field LL] [Algebra O LL] {n : ℕ}
    (M : G →* Matrix (Fin n) (Fin n) O) (θ : G →* Oˣ) (g : G) (v : Fin n → LL) :
    ((twistM M θ g).map (algebraMap O LL)).mulVec v = ((θ g : Oˣ) : O) • ((M g).map (algebraMap O LL)).mulVec v := by
  have : (twistM M θ g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (M g).map (algebraMap O LL) := by
    ext i j
    change algebraMap O LL (((θ g : Oˣ) : O) * M g i j) = ((θ g : Oˣ) : O) • algebraMap O LL (M g i j)
    rw [map_mul, Algebra.smul_def]
  rw [this, Matrix.smul_mulVec]

private theorem mulVec_smul_scalar {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) LL) (s : O) (v : Fin n → LL) : M.mulVec (s • v) = s • M.mulVec v := by
  rw [Matrix.mulVec_smul]

private theorem tmul_surjective_rank_one {O T X : Type} [CommRing O] [AddCommGroup T] [Module O T] [AddCommGroup X] [Module O X]
    (x₀ : X) (h : ∀ x : X, ∃ c : O, x = c • x₀) (m : T ⊗[O] X) : ∃ t : T, t ⊗ₜ[O] x₀ = m :=
  _root_.UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one x₀ h m

theorem _root_.UpperTheory.KN.exists_admissible_extension_latticeTensor :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ : G →* Oˣ) (p : Xs)
      {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
      (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (z : G → ↥L.T ⊗[O] X)
      (iW : V →ₗ[LL] (Fin n → LL)) (e : Fin n → LL) (x₀ : X),
      χ = θ → lam ≠ 0 → (∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ)))) →
      HasPres LL N (fun g => tableLineDegreeTwo.actTw L X χ g) z →
      Function.Injective iW → (∀ g v, iW (ρ g v) = ((θ g : Oˣ) : O) • ((N p g).map (algebraMap O LL)).mulVec (iW v)) →
      e ≠ 0 → (∀ g, ((N p g).map (algebraMap O LL)).mulVec e = e) → (∀ x : X, ∃ c : O, x = c • x₀) →
      ∀ b : ℕ, (∀ x : X, lam ^ b • x = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT (tableLineDegreeTwo.actExt L X χ z) (tableLineDegreeTwo.kerExt L X lam b) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    Xs n N θ χ p V _ _ _ _ ρ L X _ _ z iW e x₀ hχ hlam hfull hpres hiW hρ he hfix hx₀ b hb
  subst hχ
  obtain ⟨a, x, E, Y, hfg, hst, hE, φ, hφ, hz⟩ := hpres
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
  haveI : Module.IsTorsionFree O (Fin n → LL) := Module.IsTorsionFree.trans_faithfulSMul O LL _
  let j : (↥Y × ↥L.T × O) →ₗ[O] ((Fin a ⊕ Bool) → Fin n → LL) :=
    { toFun := fun u => Sum.elim (fun k => (u.1 : Fin a → Fin n → LL) k + u.2.2 • E k)
        (fun c => cond c (iW (u.2.1 : V)) (u.2.2 • e))
      map_add' := by
        intro u v
        funext k
        rcases k with k | _ | _
        · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, add_smul]
          abel
        · simp [add_smul]
        · simp
      map_smul' := by
        intro c u
        funext k
        rcases k with k | _ | _
        · simp [mul_smul, smul_add]
        · simp [mul_smul]
        · simp }
  let actA : G → (↥Y × ↥L.T × O) → (↥Y × ↥L.T × O) := fun g u =>
    (((χ g : Oˣ) : O) • (⟨_, hst g u.1.1 u.1.2⟩ : ↥Y) + (u.2.2 * ((χ g : Oˣ) : O)) • (⟨_, hE g⟩ : ↥Y),
      actT L g u.2.1, ((χ g : Oˣ) : O) * u.2.2)
  let q0 : (↥Y × ↥L.T × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
    LinearMap.prod (φ ∘ₗ LinearMap.fst O _ _ +
        (TensorProduct.mk O ↥L.T X).flip x₀ ∘ₗ LinearMap.fst O _ _ ∘ₗ LinearMap.snd O _ _)
      (LinearMap.snd O _ _ ∘ₗ LinearMap.snd O _ _)
  have hq0 : ∀ u, q0 u = (φ u.1 + u.2.1 ⊗ₜ[O] x₀, u.2.2) := fun u => rfl
  have hq0a : ∀ g u, q0 (actA g u) = tableLineDegreeTwo.actExt L X χ z g (q0 u) := by
    intro g u
    rw [hq0, hq0]
    simp only [actA, tableLineDegreeTwo.actExt, map_add, map_smul, hφ, ← hz, tableLineDegreeTwo.actTw, LinearMap.smul_apply, smul_smul,
      Units.mul_inv, one_smul, LinearMap.rTensor_tmul]
    refine Prod.ext ?_ rfl
    simp only
    abel
  refine UpperTheory.KN.exists_admissible_lattice_matrix_of_period_data PD emb lam jT cT (fun k : Fin a ⊕ Bool => twistM (N (Sum.elim x (fun _ => p) k)) χ)
    j actA _ _ ((tableLineDegreeTwo.kerExt L X lam b).mkQ ∘ₗ q0) (lam ^ b) (fun k => hfull _) ?_ ?_ ?_ ?_ (pow_ne_zero _ hlam)
    (GlobalTheory.UseLoc.Cases.AdmW.kerExt_kill L X lam b hb)
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, t, s⟩ h
    have h1 : s • e = 0 := congrFun h (Sum.inr false)
    have h2 : iW (t : V) = 0 := congrFun h (Sum.inr true)
    have hs : s = 0 := (smul_eq_zero.mp h1).resolve_right he
    have ht : t = 0 := Subtype.ext (hiW (h2.trans (map_zero iW).symm))
    have hy : y = 0 := by
      apply Subtype.ext
      funext k
      have h3 : (y : Fin a → Fin n → LL) k + s • E k = 0 := congrFun h (Sum.inl k)
      rw [hs, zero_smul, add_zero] at h3
      exact h3
    rw [hs, ht, hy]
    rfl
  · rintro g ⟨y, t, s⟩
    funext k
    unfold actN
    rw [twisted_matrix_mulVec_base_change]
    rcases k with k | _ | _
    · change ((χ g : Oˣ) : O) • ((N (x k) g).map (algebraMap O LL)).mulVec ((y : Fin a → Fin n → LL) k) +
          (s * ((χ g : Oˣ) : O)) • (((N (x k) g).map (algebraMap O LL)).mulVec (E k) - E k) +
          (((χ g : Oˣ) : O) * s) • E k =
        ((χ g : Oˣ) : O) • ((N (x k) g).map (algebraMap O LL)).mulVec ((y : Fin a → Fin n → LL) k + s • E k)
      rw [Matrix.mulVec_add, mulVec_smul_scalar, smul_add, smul_smul, mul_comm s, smul_sub]
      abel
    · change (((χ g : Oˣ) : O) * s) • e = ((χ g : Oˣ) : O) • ((N p g).map (algebraMap O LL)).mulVec (s • e)
      rw [mulVec_smul_scalar, hfix, smul_smul]
    · exact hρ g (t : V)
  · refine (Submodule.mkQ_surjective _).comp ?_
    rintro ⟨m, s⟩
    obtain ⟨t, rfl⟩ := tmul_surjective_rank_one x₀ hx₀ m
    exact ⟨(0, t, s), by rw [hq0]; simp⟩
  · intro g u w hw
    have hw' : q0 u - w ∈ tableLineDegreeTwo.kerExt L X lam b := (Submodule.Quotient.eq _).mp hw
    have h := GlobalTheory.UseLoc.Cases.AdmW.actExtL_ker L X χ z lam b hb g hw'
    rw [Submodule.mem_comap, map_sub, GlobalTheory.UseLoc.Cases.AdmW.actExtL_apply,
      GlobalTheory.UseLoc.Cases.AdmW.actExtL_apply, ← hq0a] at h
    exact (Submodule.Quotient.eq _).mpr h
