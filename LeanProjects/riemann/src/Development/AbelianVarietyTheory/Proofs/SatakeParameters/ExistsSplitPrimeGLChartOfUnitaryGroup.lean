import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPrimeChart

theorem entries_of_stab {R K : Type} [CommRing R] [CommRing K] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop}
    {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R) (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1)
    (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B C : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hA : ∀ y, Λ y → Λ (A *ᵥ y)) (hCB : C.map φ * B.map φ = 1) :
    ∀ i j, (C.map φ * A.map φ * B.map φ) i j ∈ OK := by
  intro i j
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  let z : Fin n → R := fun k => s ((Pi.single j (1 : K) : Fin n → K) k)
  have hz : ∀ k, O (z k) := fun k => hO' _ (by
    by_cases hk : k = j
    · subst hk; simp [one_mem]
    · simp [hk, zero_mem])
  have hz' : φ ∘ z = Pi.single j 1 := funext fun k => hs _
  obtain ⟨z', hz1, hz2⟩ := h2 _ (hA _ (h1 z hz))
  have e1 : A.map φ *ᵥ (B.map φ *ᵥ Pi.single j 1) = B.map φ *ᵥ (φ ∘ z') := by
    have := congrArg (φ ∘ ·) hz2
    simp only [sm] at this
    rw [mv, sm, mv, hz', mv] at this
    exact this
  have e2 : (C.map φ * A.map φ * B.map φ) i j = (φ ∘ z') i := by
    have : (C.map φ * A.map φ * B.map φ) *ᵥ Pi.single j 1 = φ ∘ z' := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
    have := congrFun this i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rw [e2]
  exact hO _ (hz1 i)

theorem conj_mul_eq_one {K : Type} [CommRing K] {n : ℕ} {X Y Z W : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1)
    (h2 : X * Y = 1) (h3 : Z * W = 1) : X * Z * Y * (X * W * Y) = 1 := by
  calc X * Z * Y * (X * W * Y) = X * (Z * ((Y * X) * (W * Y))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, ← Matrix.mul_assoc Z, h3, Matrix.one_mul, h2]

theorem conj_conj {K : Type} [CommRing K] {n : ℕ} {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1) :
    Y * (X * Z * Y) * X = Z := by
  calc Y * (X * Z * Y) * X = (Y * X) * Z * (Y * X) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitPrimeChart

namespace GlobalTheory.SplitPrimeChart

open Formalism.L2.NTheta

set_option maxHeartbeats 1000000 in

theorem exists_chart : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  intro D V P e he ϖ h1 h2
  have hee' : e * e = e := he.1.1
  have ht := GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (P := P) (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨φ, s, hs, hε, hφ, hO, hO', hinc⟩ := GlobalTheory.SphLabelOps.exists_component hee' ht
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V hee' ht
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, hee']
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  let b : GL (Fin V.rank) (P.adicCompletion D.host.E) := ⟨B.map φ, C.map φ, mp _ _ c1, mp _ _ c2⟩
  let ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E) :=
    (MulAut.conj b⁻¹).toMonoidHom.comp ((Formalism.UG.bc φ).comp (finHom V))
  have hρ : ∀ g, ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      C.map φ * (finMat D.sp.cm.sig V.gram g).map φ * B.map φ := fun g => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
    rfl
  refine ⟨ρ, fun M => ?_, fun k hk => ?_, fun g a k₁ hk₁ k₂ hk₂ hg => ?_⟩
  · have hsM : ∀ N : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E), (N.map s).map φ = N :=
      fun N => Matrix.ext fun i j => hs _
    have hm : finPart D e • ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)) =
        finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      apply hφ
      have : ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)).map φ =
          (1 : Matrix (Fin V.rank) (Fin V.rank) _).map φ := by
        simp only [Matrix.map_mul]
        rw [Matrix.map_one φ (map_zero φ) (map_one φ), hsM, hsM]
        exact conj_mul_eq_one (mp _ _ c2) (mp _ _ c1) (Units.mul_inv M)
      exact congrFun (congrFun this i) j
    obtain ⟨g, hgs, hg⟩ := GlobalTheory.SplitLift.split_lift V e he.1 _ _ hm
    refine ⟨g, hgs, Units.ext ?_⟩
    have hgm : (finMat D.sp.cm.sig V.gram g).map φ = (B * (M : Matrix _ _ _).map s * C).map φ :=
      Matrix.ext fun i j => by
        have := congrArg φ (congrFun (congrFun hg i) j)
        rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
          one_mul] at this
    rw [hρ, hgm, Matrix.map_mul, Matrix.map_mul, hsM]
    exact conj_conj (mp _ _ c2)
  · have hint : ∀ g ∈ KsphC V ∅, ∀ i j,
        ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) i j ∈
          Formalism.UG.Ov D.host.E P := by
      intro g hg i j
      rw [hρ]
      exact entries_of_stab (Λ := fun y => y ∈ LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1
        (fun y hy => b2 y hy) (fun y hy => (hg.2.1 y).1 hy) (mp _ _ c2) i j
    have hk' : k⁻¹ ∈ KsphC V ∅ :=
      (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG k).2 hk))
    refine Formalism.UG.P.cartan_mem_of_entries _ _ (hint k hk) ?_
    rw [← map_inv]
    exact hint _ hk'
  · rw [GlobalTheory.DivDual.divAt_iff]
    refine ⟨List.length_ofFn, GlobalTheory.SphLabelOps.dv_of_cartan φ s hs hε hφ hO hO' (B := B) b1 b2
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂)) ?_⟩
    have e1 : (Matrix.diagonal fun i : Fin V.rank =>
        φ (finPart D (incA D ((ϖ : D.host.E) ^ ((List.ofFn a).getD i.1 0))))) =
        Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) a := by
      unfold Formalism.UG.diagPow
      congr 1
      funext i
      rw [hinc, map_zpow₀]
      simp
    rw [e1, ← hg, hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mp _ _ c1, Matrix.one_mul]

end GlobalTheory.SplitPrimeChart
