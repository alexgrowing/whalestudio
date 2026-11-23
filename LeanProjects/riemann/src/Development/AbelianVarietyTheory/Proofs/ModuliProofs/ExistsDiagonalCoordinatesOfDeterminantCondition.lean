import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DiagCoord

theorem exists_linearIndependent_of_iSupIndep {k V I T : Type} [Field k] [AddCommGroup V] [Module k V] [Finite I]
    (W : T → Submodule k V) (hW : iSupIndep W) (ty : I → T)
    (b : ∀ τ, Nonempty (Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ))) :
    ∃ v : I → V, LinearIndependent k v ∧ ∀ i, v i ∈ W (ty i) := by
  classical
  let B : ∀ τ, Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ) := fun τ => (b τ).some
  let e : ∀ τ, {i // ty i = τ} ≃ Fin (Nat.card {i // ty i = τ}) := fun τ => Finite.equivFin _
  let f : ∀ τ, {i // ty i = τ} → V := fun τ j => ((B τ (e τ j) : W τ) : V)
  have hmem : ∀ τ j, f τ j ∈ W τ := fun τ j => (B τ (e τ j)).2
  have hspan : ∀ τ, Submodule.span k (Set.range (f τ)) ≤ W τ := by
    intro τ
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem τ j
  have hsig : LinearIndependent k (fun p : Σ τ, {i // ty i = τ} => f p.1 p.2) := by
    refine linearIndependent_iUnion_finite (fun τ => ?_) (fun τ t _ hτ => ?_)
    · exact ((B τ).linearIndependent.map' (W τ).subtype (Submodule.ker_subtype _)).comp
        (e τ) (e τ).injective
    · exact (hW.disjoint_biSup hτ).mono (hspan τ) (iSup₂_mono fun σ _ => hspan σ)
  let s : I → Σ τ, {i // ty i = τ} := fun i => ⟨ty i, ⟨i, rfl⟩⟩
  have hs : Function.Injective s := fun i j h => congrArg (fun p : Σ τ, {i // ty i = τ} => (p.2 : I)) h
  exact ⟨fun i => f (ty i) ⟨i, rfl⟩, hsig.comp s hs, fun i => hmem (ty i) ⟨i, rfl⟩⟩

open GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Chart in

theorem exists_diff_linear {O : Type} [CommRing O] {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (act : OAct O A) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ d : Serre.Lie act →ₗ[ℂ] (Fin g → ℂ), Function.Injective d ∧ ∀ v, u.IsDiff (d v) v.hom := by
  classical
  let dd : Serre.Lie act → (Fin g → ℂ) := fun v => (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose
  have hdd : ∀ v : Serre.Lie act, u.IsDiff (dd v) v.hom := fun v =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose_spec
  have huniq : ∀ (v : Serre.Lie act) (w : Fin g → ℂ), u.IsDiff w v.hom → dd v = w := fun v w hw =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).unique (hdd v) hw
  have hcomb : ∀ (n : ℕ) (r : Fin n → ℂ) (vs : Fin n → Serre.Lie act),
      u.IsDiff (∑ i, r i • dd (vs i)) (∑ i, r i • vs i).hom := fun n r vs =>
    GlobalTheory.UnifDifferential.isDiff_of_isLieComb A L g n u (fun i => dd (vs i)) (fun i => (vs i).hom) r _
      (fun i => GlobalTheory.Serre.Lie.isTangent (vs i)) (fun i => hdd (vs i))
      ((GlobalTheory.Serre.Lie.isLieComb_iff r vs _).2 rfl)
  have hadd : ∀ v w : Serre.Lie act, dd (v + w) = dd v + dd w := by
    intro v w
    apply huniq
    have h2 := hcomb 2 ![1, 1] ![v, w]
    simpa [Fin.sum_univ_two] using h2
  have hsmul : ∀ (c : ℂ) (v : Serre.Lie act), dd (c • v) = c • dd v := by
    intro c v
    apply huniq
    have h1 := hcomb 1 ![c] ![v]
    simpa using h1
  refine ⟨{ toFun := dd, map_add' := hadd, map_smul' := hsmul }, ?_, hdd⟩
  intro v w hvw
  apply GlobalTheory.Serre.Lie.ext
  have hw : u.IsDiff (dd v) w.hom := by
    have := hdd w
    have hvw' : dd v = dd w := hvw
    rwa [← hvw'] at this
  exact (h₂ (dd v)).unique ⟨GlobalTheory.Serre.Lie.isTangent v, hdd v⟩ ⟨GlobalTheory.Serre.Lie.isTangent w, hw⟩

end GlobalTheory.DiagCoord

open GlobalTheory.DiagCoord GlobalTheory.Serre in

theorem GlobalTheory.exists_diagonal_coordinates_of_detCond :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  intro _ _ _ _ E _ _ _ H D P u Hm χ act ty _ hty hdet
  unfold DetCond at hdet
  unfold IsTypeFn at hty
  have : IsCommMonObj P.A := Out.PolAV.isCommMonObj P
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u P.smoothDim
  obtain ⟨d, hdinj, hdd⟩ := exists_diff_linear u act h₁ h₂
  let ty' : Fin P.g → (𝓞 E →+* ℂ) := fun i => (ty i).comp (algebraMap (𝓞 E) E)
  have hinj : ∀ τ : 𝓞 E →+* ℂ, Function.Injective τ := by
    intro τ
    refine (RingHom.injective_iff_ker_eq_bot τ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
    ext n
    simp [RingHom.mem_ker]
  have hcard : ∀ τ : 𝓞 E →+* ℂ, ∃ σ : E →+* ℂ, σ (H.rt : E) = τ H.rt ∧
      Nat.card {i // ty' i = τ} = Nat.card {i // ty i = σ} := by
    intro τ
    refine ⟨IsFractionRing.lift (hinj τ), IsFractionRing.lift_algebraMap (hinj τ) H.rt,
      Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun hi => ?_, fun hi => ?_⟩)⟩
    · refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
      exact congrArg (fun f : 𝓞 E →+* ℂ => f x) hi
    · refine RingHom.ext fun x => ?_
      show ty i (algebraMap (𝓞 E) E x) = τ x
      rw [hi]
      exact IsFractionRing.lift_algebraMap (hinj τ) x
  have hb : ∀ τ : 𝓞 E →+* ℂ,
      Nonempty (Module.Basis (Fin (Nat.card {i // ty' i = τ})) ℂ (GlobalTheory.Serre.Lie.eig act τ)) := by
    intro τ
    obtain ⟨σ, hσ, hc⟩ := hcard τ
    refine (GlobalTheory.Serre.Lie.lieMult_id_iff act τ _).1 ?_
    rw [hc]
    by_cases hτ : τ H.rt = H.rt0
    · rw [(hty σ).1 (hσ.trans hτ)]
      exact (hdet τ).1 hτ
    · rw [(hty σ).2 (fun h => hτ (hσ.symm.trans h))]
      exact (hdet τ).2 hτ
  obtain ⟨v, hvli, hvmem⟩ :=
    exists_linearIndependent_of_iSupIndep (GlobalTheory.Serre.Lie.eig act) (GlobalTheory.Serre.Lie.iSupIndep_eig act) ty' hb
  choose F hF using fun a : 𝓞 E =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV P P P.L P.L u u (act.act a) (act.hom a)
  have key : ∀ (a : 𝓞 E) (i : Fin P.g), F a (d (v i)) = ty i (a : E) • d (v i) := by
    intro a i
    have := act.hom a
    have e1 := GlobalTheory.HomLinear.isDiff_comp u u (act.act a) (F a) (hF a)
      (GlobalTheory.Serre.Lie.isTangent (v i)) (hdd (v i))
    have hv : a • v i = ty' i a • v i := (GlobalTheory.Serre.Lie.mem_eig_iff.1 (hvmem i)) a
    have e2 : (ty' i a • v i).hom = (v i).hom ≫ act.act a := by
      rw [← hv, GlobalTheory.Serre.Lie.hom_act_smul]
    rw [← e2] at e1
    have e3 := hdd (ty' i a • v i)
    rw [map_smul] at e3
    exact (h₁ _ (GlobalTheory.Serre.Lie.isTangent _)).unique e1 e3
  have hli : LinearIndependent ℂ (d ∘ v) := hvli.map' d (LinearMap.ker_eq_bot.2 hdinj)
  let B : Module.Basis (Fin P.g) ℂ (Fin P.g → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank' (d ∘ v) hli (by simp)
  have hB : ∀ i, B i = d (v i) := fun i => by simp [B]
  refine ⟨B.equivFun.symm, fun a z => ?_⟩
  rw [← hF a]
  refine congrArg u.ex ?_
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hB, key, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
