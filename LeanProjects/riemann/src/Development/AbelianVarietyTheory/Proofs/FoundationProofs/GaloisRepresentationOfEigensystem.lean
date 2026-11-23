import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElementStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjoinStableAndCommutes
set_option maxHeartbeats 1600000

noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) : X.gal (s * s') f = X.gal s (X.gal s' f) := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp, AlgEquiv.mul_apply]

theorem gal_one_apply (X : Tower Ω ε) (f : X.K) : X.gal 1 f = f := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal 1 f)).coeff r = (X.exp f).coeff r
  rw [X.gal_exp, AlgEquiv.one_apply]

theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) :
    X.kmap l φ ∘ₗ X.kmap l ψ = X.kmap l (ψ.trans φ) := by
  letI := X.fld
  unfold Tower.kmap
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [← LinearMap.comp_apply (AdicCompletion.map _ _), AdicCompletion.map_comp, ← LinearMap.baseChange_comp]
  have h : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) =
      AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (ψ.trans φ).toMonoidHom)) := by
    ext u; rfl
  rw [h]

theorem kmap_refl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.kmap l (RingEquiv.refl X.K) = LinearMap.id := by
  letI := X.fld
  unfold Tower.kmap
  have h : AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom)) =
      LinearMap.id := by
    ext u; rfl
  rw [h, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) :
    X.galB l (s * s') = X.galB l s ∘ₗ X.galB l s' := by
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := RingEquiv.ext (gal_mul_apply X s s')
  have hr : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (X.kmap l (X.gal s)), kmap_comp, ← hg, hr, map_mul, Units.val_mul]
  congr 2
  ext i; fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem galB_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.galB l 1 = LinearMap.id := by
  have hg : X.gal 1 = RingEquiv.refl X.K := RingEquiv.ext (gal_one_apply X)
  have hr : (1 : Ω ≃ₐ[ℚ] Ω).toRingEquiv = 1 := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [hg, kmap_refl, hr, map_one, Units.val_one, one_mul, LinearMap.id_apply]
  congr 1
  ext i; fin_cases i <;> rfl

section BC
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] (E : Type) [Field E] [Algebra R E]
  (B : Submodule R M)

theorem bc_mem (f : M →ₗ[R] M) (hf : ∀ b ∈ B, f b ∈ B) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f x ∈ LinearMap.range (LinearMap.baseChange E B.subtype) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨LinearMap.baseChange E (f.restrict hf) y, ?_⟩
  have h : B.subtype ∘ₗ f.restrict hf = f ∘ₗ B.subtype := LinearMap.ext fun b => rfl
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

theorem bc_comm (f g : M →ₗ[R] M) (hfg : ∀ b ∈ B, f (g b) = g (f b)) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f (LinearMap.baseChange E g x) = LinearMap.baseChange E g (LinearMap.baseChange E f x) := by
  obtain ⟨y, rfl⟩ := hx
  have h : f ∘ₗ g ∘ₗ B.subtype = g ∘ₗ f ∘ₗ B.subtype := LinearMap.ext fun b => hfg b b.2
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

end BC

section Gen
variable {E V G : Type} [Field E] [AddCommGroup V] [Module E V]

theorem adj_eigen (A : Set Letter) (f : Letter → Module.End E V) (lam : Letter → E) (y : V)
    (hy : ∀ T ∈ A, f T y = lam T • y) (Q : FreeAlgebra E Letter)
    (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    FreeAlgebra.lift E f Q y = FreeAlgebra.lift E lam Q • y := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [FreeAlgebra.lift_ι_apply, hy T hT]
  | algebraMap r => simp
  | add a b _ _ ha hb => simp [ha, hb, add_smul]
  | mul a b _ _ ha hb => simp [Module.End.mul_apply, ha, hb, smul_smul, mul_comm]

theorem adj_stab (A : Set Letter) (f : Letter → Module.End E V) (W : Submodule E V) (g : G → Module.End E V)
    (hs : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) (hc : ∀ T ∈ A, ∀ s, ∀ x ∈ W, f T (g s x) = g s (f T x))
    (Q : FreeAlgebra E Letter) (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    ∀ x ∈ W, FreeAlgebra.lift E f Q x ∈ W ∧ ∀ s, g s (FreeAlgebra.lift E f Q x) = FreeAlgebra.lift E f Q (g s x) := by
  first
  | exact @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | (apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes ..)

end Gen

end GlobalTheory.KZ.HeckeProj

namespace GlobalTheory.KZ.HeckeProj

theorem heckeProj_main : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw E _ _ _ hnorm lam hSS ρ S0 htc hdc hfr hirr
  obtain ⟨P, hPadm, hP1, hPe⟩ := hSS
  have hgal : ∀ s, ∀ x ∈ X.VB N l w E, X.galV l E s x ∈ X.VB N l w E := fun s x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.galB l s) (GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s) x hx
  have hstab : ∀ T ∈ {T | admitted N l T}, ∀ x ∈ X.VB N l w E, X.opV N l E T x ∈ X.VB N l w E := fun T hT x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.op N l T) (GlobalTheory.T.hecke_letter_preserves_basis_set ε X hε hj N l w hl hN hNl hw T hT) x hx
  have hcomm : ∀ T ∈ {T | admitted N l T}, ∀ s, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.galV l E s x) = X.galV l E s (X.opV N l E T x) := fun T hT s x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.galB l s)
      (fun b hb => GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl hN hNl hw T hT s b hb) x hx
  have hfin : Module.Finite ℤ_[l] (X.B N l w) := (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl hN hNl hw).2
  have hVBfin : FiniteDimensional E (X.VB N l w E) := by
    unfold Tower.VB; infer_instance
  set Pv := FreeAlgebra.lift E (X.opV N l E) P with hPv
  have hPst := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E) (X.galV l E) hstab hcomm P hPadm
  have heig : ∀ x ∈ X.VB N l w E, ∀ T, admitted N l T → X.opV N l E T (Pv x) = lam T • Pv x := by
    intro x hx T hT
    have := hPe x hx T hT
    simpa [sub_eq_zero] using this
  have hfix : ∀ y, (∀ T, admitted N l T → X.opV N l E T y = lam T • y) → Pv y = y := by
    intro y hy
    have := HeckeProj.adj_eigen {T | admitted N l T} (X.opV N l E) lam y hy P hPadm
    rw [hP1, one_smul] at this
    exact this
  set U : Submodule E (E ⊗[ℤ_[l]] X.Fn l) := (X.VB N l w E).map Pv with hU
  have hUVB : ∀ u ∈ U, u ∈ X.VB N l w E := by
    rintro u ⟨x, hx, rfl⟩; exact (hPst x hx).1
  have hUeig : ∀ u ∈ U, ∀ T, admitted N l T → X.opV N l E T u = lam T • u := by
    rintro u ⟨x, hx, rfl⟩; exact heig x hx
  have hUfix : ∀ u ∈ U, Pv u = u := fun u hu => hfix u (hUeig u hu)
  have hUgal : ∀ s, ∀ u ∈ U, X.galV l E s u ∈ U := by
    rintro s u ⟨x, hx, rfl⟩
    exact ⟨X.galV l E s x, hgal s x hx, ((hPst x hx).2 s).symm⟩
  haveI : FiniteDimensional E U := by rw [hU]; infer_instance
  have hgm : ∀ s s', X.galV l E (s * s') = X.galV l E s * X.galV l E s' := by
    intro s s'
    simp only [Tower.galV, HeckeProj.galB_mul, LinearMap.baseChange_comp, Module.End.mul_eq_comp]
  have hg1 : X.galV l E 1 = 1 := by
    simp only [Tower.galV, HeckeProj.galB_one, LinearMap.baseChange_id, Module.End.one_eq_id]
  let σU : (Ω ≃ₐ[ℚ] Ω) →* Module.End E U :=
    { toFun := fun s => (X.galV l E s).restrict (hUgal s)
      map_one' := by
        ext u; simp [LinearMap.restrict_apply, hg1]
      map_mul' := by
        intro s s'; ext u; simp [LinearMap.restrict_apply, hgm, Module.End.mul_apply] }
  have hσU : ∀ s (u : U), ((σU s u : U) : E ⊗[ℤ_[l]] X.Fn l) = X.galV l E s u := fun s u => rfl
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] E 2 = 0 := by rw [map_ofNat]; exact h
    have := hnorm 2
    rw [h', norm_zero] at this
    have h0 : (2 : ℤ_[l]) = 0 := norm_eq_zero.mp this.symm
    exact two_ne_zero h0
  have hCH : ∀ g, σU g * σU g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σU g +
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0 := by
    intro g
    ext u
    have hu := GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element ε X hε hj N l w hl hN hNl hw hnorm lam
      (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E))
      S0 htc hdc hfr (u : E ⊗[ℤ_[l]] X.Fn l) (hUVB u u.2) (hUeig u u.2) g
    simpa [Module.End.mul_apply, hσU] using hu
  obtain ⟨m, π', s', h1, h2', h3, h4⟩ := GlobalTheory.T.two_dim_rep_quadratic_relation h2 ρ hirr σU hCH
  let Pr : X.VB N l w E →ₗ[E] U :=
    LinearMap.codRestrict U (Pv ∘ₗ (X.VB N l w E).subtype) (fun x => Submodule.mem_map_of_mem x.2)
  have hext : ∀ i : Fin m, ∃ g : (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E),
      g ∘ₗ (X.VB N l w E).subtype = π' i ∘ₗ Pr := fun i => LinearMap.exists_extend _
  choose π hπ using hext
  have hπx : ∀ i x (hx : x ∈ X.VB N l w E), π i x = π' i (Pr ⟨x, hx⟩) := fun i x hx =>
    LinearMap.congr_fun (hπ i) ⟨x, hx⟩
  have hTT : ∀ T ∈ {T | admitted N l T}, ∀ T' : {T // admitted N l T}, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.opV N l E T'.1 x) = X.opV N l E T'.1 (X.opV N l E T x) := fun T hT T' x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.op N l T'.1)
      (fun b hb => GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X hε hj N l w hl hN hNl hw T T'.1 hT T'.2 b hb) x hx
  have hPT := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E)
    (fun T' : {T // admitted N l T} => X.opV N l E T'.1) hstab hTT P hPadm
  have hsumP : ∀ x ∈ X.VB N l w E, Pv x = ∑ i, (U.subtype ∘ₗ s' i) (π i x) := by
    intro x hx
    have := LinearMap.congr_fun h4 (Pr ⟨x, hx⟩)
    have e2 : (∑ i, s' i (π' i (Pr ⟨x, hx⟩))) = Pr ⟨x, hx⟩ := by simpa [LinearMap.sum_apply] using this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, hπx _ x hx]
    rw [← Submodule.coe_sum, e2]
    rfl
  refine ⟨m, π, fun i => U.subtype ∘ₗ s' i, P, hPadm, hP1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hxe
    rw [← hsumP x hx]
    exact hfix x hxe
  · intro i v
    exact hUVB _ (s' i v).2
  · intro i s x hx
    rw [hπx i _ (hgal s x hx), hπx i x hx]
    have e : Pr ⟨X.galV l E s x, hgal s x hx⟩ = σU s (Pr ⟨x, hx⟩) := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, hσU]
      exact ((hPst x hx).2 s).symm
    rw [e]
    have := LinearMap.congr_fun (h1 i s) (Pr ⟨x, hx⟩)
    simpa [Matrix.toLin'_apply] using this
  · intro i s v
    have := LinearMap.congr_fun (h2' i s) v
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [← hσU, this]
    simp [Matrix.toLin'_apply]
  · intro i T v hT
    exact hUeig _ (s' i v).2 T hT
  · intro i T hT x hx
    have hTx := hstab T hT x hx
    rw [hπx i _ hTx, hπx i x hx]
    have e : Pr ⟨X.opV N l E T x, hTx⟩ = lam T • Pr ⟨x, hx⟩ := by
      apply Subtype.ext
      have hc := (hPT x hx).2 ⟨T, hT⟩
      simp only at hc
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul]
      rw [← hc]
      exact hUeig _ (Submodule.mem_map_of_mem hx) T hT
    rw [e, map_smul]
  · intro i j v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hπx i _ (hUVB _ (s' j v).2)]
    have e : Pr ⟨((s' j v : U) : E ⊗[ℤ_[l]] X.Fn l), hUVB _ (s' j v).2⟩ = s' j v := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact hUfix _ (s' j v).2
    rw [e]
    have := LinearMap.congr_fun (h3 i j) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    split_ifs <;> simp
  · intro x hx
    exact hsumP x hx

end GlobalTheory.KZ.HeckeProj
