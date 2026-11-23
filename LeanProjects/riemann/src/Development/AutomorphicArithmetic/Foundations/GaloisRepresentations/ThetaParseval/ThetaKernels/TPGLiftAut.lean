import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.LiftAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNhdsOneWeilFixesPureTensor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepMemPolynomialFockOfArchimedean
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepMemPolynomialFockOfFinitePlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EndEgrpMatch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LevelK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaLiftWeilTranslateEquivariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThetaLiftOfDefinite
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFiniteDimensionalWeilArchimedeanOrbit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaLiftLinearInSchwartz

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
open PositivityTheory.ThKEnd.Grp in
private theorem stab_of_pk {m : ℕ} {Y : Spc F E m} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : UA σ Y.J →* Module.End ℂ V) (P : Submodule ℂ V)
    (hlev : ∀ Φ ∈ P, ∀ᶠ u in 𝓝 (1 : UA σ Y.J), (∀ w, (mat u).map (piInf (τ w)) = 1) → A u Φ = Φ)
    (hr : ∀ g ∈ UAt σ Y (evI F), ∀ Φ ∈ P, A g Φ ∈ P)
    (hl : ∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ P, A g Φ ∈ P) (g : UA σ Y.J) : ∀ Φ ∈ P, A g Φ ∈ P := by
  intro Φ hΦ
  have h1 : Tendsto (fun S : Finset (Pl F) => (piece (eps S) (eps_sq S) g)⁻¹ * g) atTop (𝓝 1) := by
    rw [← inv_mul_cancel g]
    exact (tendsto_piece g).inv.mul_const g
  obtain ⟨S, h2⟩ := (h1.eventually (hlev Φ hΦ)).exists
  have h4 : ∀ w, (mat ((piece (eps S) (eps_sq S) g)⁻¹ * g)).map (piInf (τ w)) = 1 := fun w => by
    rw [mat_mul, Matrix.map_mul, ← piInf_piece S g, ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨l, l1, l2⟩ := piece_prod g S
  have e : g = piece (eps ∅) (eps_sq ∅) g * l.prod * ((piece (eps S) (eps_sq S) g)⁻¹ * g) := by
    rw [← l2, mul_inv_cancel_left]
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h2 h4]
  refine hr _ (piece_inf g) _ ?_
  clear e h2 h4 l2
  induction l with
  | nil => simpa using hΦ
  | cons x l ih =>
    obtain ⟨v, hv⟩ := l1 x List.mem_cons_self
    rw [List.prod_cons, map_mul, Module.End.mul_apply]
    exact hl v x hv _ (ih fun h hh => l1 h (List.mem_cons_of_mem _ hh))
variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
theorem levelX_sch_k {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (u, 1) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := _root_.UpperTheory.exists_nhds_one_weil_fixes_pure_tensor F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add, h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
theorem polStab_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) (x : UA σ X.J) (y : UA σ W.J) :
    ∀ Φ ∈ PolData B M, om (x, y) Φ ∈ PolData B M := by
  have hsch : ∀ Φ ∈ PolData B M, Φ ∈ schA F (Fin n × Fin d) := fun Φ h => PositivityTheory.ThKG.polData_le hp.good h
  have o1 : ∀ {m : ℕ} {v : Pl F} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun Y => PositivityTheory.ThKH.Locrep.one_mem_UAt (σ := σ) Y _
  have o2 : ∀ {m : ℕ} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := fun Y u _ => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  have e : ((x, y) : UA σ X.J × UA σ W.J) = (x, 1) * (1, y) := by simp
  intro Φ hΦ
  rw [e, map_mul, Module.End.mul_apply]
  refine stab_of_pk B.emb (om.comp (MonoidHom.inl _ _)) _ (fun Φ h => _root_.UpperTheory.TP.levelX_sch_k hp (hsch Φ h))
    (fun g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_archimedean F E σ B n d X W M χX χW om hp g hg 1 (o2 W) Φ h)
    (fun v g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v g hg 1 (o1 W) Φ h) x _ ?_
  exact stab_of_pk B.emb (om.comp (MonoidHom.inr _ _)) _
    (fun Φ h => _root_.PositivityTheory.ThKEnd.Grp.level_sch_k _root_.PositivityTheory.ThKEst.level_k hp (hsch Φ h))
    (fun g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_archimedean F E σ B n d X W M χX χW om hp 1 (o2 X) g hg Φ h)
    (fun v g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v 1 (o1 X) g hg Φ h) y _ hΦ
theorem lift_left_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (φ : UA σ X.J → ℂ) {γ : UA σ W.J} (hγ : γ ∈ ratU σ W.J) (h : UA σ W.J) : lift M om Φ φ (γ * h) = lift M om Φ φ h := by
  refine integral_congr_ae (.of_forall fun g => ?_)
  have := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hp).1 Φ hΦ
  have h2 := this.2.1 1 (one_mem _) γ hγ g h
  rw [one_mul] at h2
  show theta om Φ g (γ * h) * star (φ g) = theta om Φ g h * star (φ g)
  rw [h2]
private theorem real_of_off_pk {τ : ∀ w : InfinitePlace F, EmbOver E w} {g : UA σ W.J} (hg : g ∈ gOff σ W ∅) (w : InfinitePlace F) :
    (mat g).map (piInf (τ w)) = 1 := by
  have h : ∀ w, (mat g).map (compInf F E w) = 1 := by
    refine Subgroup.closure_induction (p := fun g _ => ∀ w, (mat g).map (compInf F E w) = 1) (fun x hx => hx.1) ?_ ?_ ?_ hg
    · intro w; exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro x y _ _ hx hy w
      rw [show mat (x * y) = mat x * mat y from rfl, Matrix.map_mul, hx, hy, one_mul]
    · intro x _ hx w
      have e : mat x⁻¹ * mat x = 1 := PositivityTheory.ThKEnd.Grp.mat_inv_mul x
      have := congrArg (fun A => A.map (compInf F E w)) e
      simp only [Matrix.map_mul, hx w, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
  have e : (mat g).map (piInf (τ w)) = ((mat g).map (compInf F E w)).map (infEmb (τ w)) := by ext i j; rfl
  rw [e, h, Matrix.map_one _ (map_zero _) (map_one _)]
end Gen
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n}
  {W : Spc (maximalRealSubfield E) E d} {B : Base (maximalRealSubfield E) E} {M : Model (cj E) X W}
  {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
theorem RU_lift_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
    {Φ : Fn (maximalRealSubfield E) n d} (hΦ : Φ ∈ schA (maximalRealSubfield E) (Fin n × Fin d)) {ψ : UA (cj E) X.J → ℂ} (hψ : IsFn ψ)
    (k : GlobalTheory.UnitaryBC.UA E d) :
    GlobalTheory.UnitaryBC.RU E d k (lift M om Φ ψ ∘ e') = lift M om (om (1, e' k) Φ) ψ ∘ e' := by
  funext h
  have := _root_.UpperTheory.thetaLift_weil_translate_equivariant T _ E (cj E) B n d X W M χX χW om hp Φ hΦ ψ hψ 1 (e' k) (e' h)
  simp only [mul_one] at this
  exact (congrArg (lift M om Φ ψ) (map_mul e' h k)).trans this.symm
theorem aut_lift_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J} (he' : IsBr W e')
    {Φ : Fn (maximalRealSubfield E) n d} (hΦ : Φ ∈ PolData B M) {ψ : UA (cj E) X.J → ℂ} (hψ : IsFn ψ) :
    GlobalTheory.UnitaryBC.IsAutFormU (lift M om Φ ψ ∘ e') := by
  have hs : Φ ∈ schA (maximalRealSubfield E) (Fin n × Fin d) := PositivityTheory.ThKG.polData_le hp.good hΦ
  refine ⟨(_root_.UpperTheory.continuous_thetaLift_of_definite T _ E (cj E) B n d X W M χX χW om hp Φ hs ψ hψ).comp e'.continuous, fun γ hγ g => ?_, ?_, ?_⟩
  · show lift M om Φ ψ (e' (γ * g)) = lift M om Φ ψ (e' g)
    rw [map_mul]
    exact _root_.UpperTheory.TP.lift_left_k T hp hs ψ ((he'.rat γ).2 hγ) _
  · let f := lift M om Φ ψ ∘ e'
    let H : Subgroup (GlobalTheory.UnitaryBC.finU E d) :=
      { carrier := {k | GlobalTheory.UnitaryBC.RU E d k f = f}
        one_mem' := by show GlobalTheory.UnitaryBC.RU E d 1 f = f; rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          show GlobalTheory.UnitaryBC.RU E d (a.1 * b.1) f = f
          rw [map_mul, Module.End.mul_apply, show GlobalTheory.UnitaryBC.RU E d b.1 f = f from hb]; exact ha
        inv_mem' := fun {a} ha => by
          show GlobalTheory.UnitaryBC.RU E d (a.1⁻¹) f = f
          have : GlobalTheory.UnitaryBC.RU E d a.1 f = f := ha
          conv_lhs => rw [← this]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    refine Subgroup.isOpen_of_mem_nhds H (g := 1) ?_
    have h1 := _root_.PositivityTheory.ThKEnd.Grp.level_sch_k _root_.PositivityTheory.ThKEst.level_k hp hs
    have c : Tendsto (fun k : GlobalTheory.UnitaryBC.finU E d => e' k.1) (𝓝 1) (𝓝 1) :=
      (e'.continuous.comp continuous_subtype_val).tendsto' _ _ (map_one e')
    filter_upwards [c.eventually h1] with k hk
    show GlobalTheory.UnitaryBC.RU E d k.1 f = f
    rw [_root_.UpperTheory.TP.RU_lift_k T hp hs hψ, hk fun w => real_of_off_pk ((he'.fin k.1).2 k.2) w]
  · obtain ⟨V, hV, hVs, hk⟩ := _root_.UpperTheory.exists_finiteDimensional_weil_archimedean_orbit _ E (cj E) B n d X W M χX χW om hp Φ hΦ
    obtain ⟨l1, l2, -, -⟩ := _root_.UpperTheory.thetaLift_linear_in_schwartz T _ E (cj E) B n d X W M χX χW om hp
    let L : V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
      { toFun := fun x => lift M om x.1 ψ ∘ e'
        map_add' := fun x y => by
          funext h
          exact congrFun (l1 x.1 (hVs x.2) y.1 (hVs y.2) ψ hψ) (e' h)
        map_smul' := fun c x => by
          funext h
          exact congrFun (l2 c x.1 (hVs x.2) ψ hψ) (e' h) }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, hk _ ((he'.inf k.1).2 k.2)⟩, (_root_.UpperTheory.TP.RU_lift_k T hp hs hψ k.1).symm⟩
end CM
theorem _root_.UpperTheory.TP.liftAut_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.LiftAut_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he'
  classical
  let C : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ GlobalTheory.UnitaryBC.ratU E n, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp only [Pi.add_apply, ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp only [Pi.smul_apply, ha.2 γ hγ g]⟩ }
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl C
  let Pj : (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) := C.subtype ∘ₗ C.linearProjOfIsCompl C' hC'
  have p1 : ∀ φ, Pj φ ∈ C := fun φ => (C.linearProjOfIsCompl C' hC' φ).2
  have p2 : ∀ φ ∈ C, Pj φ = φ := fun φ h => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC' ⟨φ, h⟩)
  have fn : ∀ φ ∈ C, IsFn (φ ∘ e.symm) := fun φ h => ⟨h.1.comp e.symm.continuous, fun γ hγ g => by
    show φ (e.symm (γ * g)) = φ (e.symm g)
    rw [map_mul]
    exact h.2 _ ((he.rat _).1 (by simpa using hγ)) _⟩
  have sch : ∀ Φ : PolData B M, Φ.1 ∈ schA (maximalRealSubfield E) (Fin n × Fin d) := fun Φ => PositivityTheory.ThKG.polData_le hP.good Φ.2
  obtain ⟨l1, l2, l3, l4⟩ := _root_.UpperTheory.thetaLift_linear_in_schwartz T _ E (cj E) B n d X W M χX χW om hP
  let Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ ψ => lift M om Φ.1 (Pj ψ ∘ e.symm) ∘ e')
      (fun Φ Φ' ψ => funext fun h => congrFun (l1 Φ.1 (sch Φ) Φ'.1 (sch Φ') _ (fn _ (p1 ψ))) (e' h))
      (fun c Φ ψ => funext fun h => congrFun (l2 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h))
      (fun Φ ψ ψ' => funext fun h => by
        have := congrFun (l3 Φ.1 (sch Φ) _ _ (fn _ (p1 ψ)) (fn _ (p1 ψ'))) (e' h)
        refine Eq.trans ?_ this
        show lift M om Φ.1 (Pj (ψ + ψ') ∘ e.symm) (e' h) = _
        rw [map_add]
        rfl)
      (fun c Φ ψ => funext fun h => by
        have := congrFun (l4 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h)
        refine Eq.trans ?_ this
        show lift M om Φ.1 (Pj (c • ψ) ∘ e.symm) (e' h) = _
        rw [map_smul]
        rfl)
  have q : ∀ (Φ₀ : PolData B M) (φ₀ : GlobalTheory.UnitaryBC.UA E n → ℂ), φ₀ ∈ C → Θ Φ₀ φ₀ = lift M om Φ₀.1 (φ₀ ∘ e.symm) ∘ e' :=
    fun Φ₀ φ₀ h => by
      show lift M om Φ₀.1 (Pj φ₀ ∘ e.symm) ∘ e' = _
      rw [p2 _ h]
  refine ⟨Θ, fun Φ φ hφ => ?_⟩
  have hφC : φ ∈ C := ⟨hφ.cont, hφ.left⟩
  refine ⟨q Φ φ hφC, by rw [q _ _ hφC]; exact _root_.UpperTheory.TP.aut_lift_k T hP he' Φ.2 (fn φ hφC), fun g h => ?_⟩
  have hm := _root_.UpperTheory.TP.polStab_k T hP (e g) (e' h) Φ.1 Φ.2
  refine ⟨⟨_, hm⟩, rfl, ?_⟩
  have hRC : GlobalTheory.UnitaryBC.RU E n g φ ∈ C :=
    ⟨hφ.cont.comp (continuous_mul_right g), fun γ hγ x => by
      show φ (γ * x * g) = φ (x * g)
      rw [mul_assoc]
      exact hφ.left γ hγ _⟩
  rw [q _ _ hRC, q _ _ hφC]
  funext h₀
  have := _root_.UpperTheory.thetaLift_weil_translate_equivariant T _ E (cj E) B n d X W M χX χW om hP Φ.1 (sch Φ) (φ ∘ e.symm) (fn φ hφC) (e g) (e' h) (e' h₀)
  have e1 : GlobalTheory.UnitaryBC.RU E n g φ ∘ e.symm = fun y => (φ ∘ e.symm) (y * e g) := by
    funext y
    show φ (e.symm y * g) = φ (e.symm (y * e g))
    rw [map_mul, e.symm_apply_apply]
  rw [e1]
  refine this.trans ?_
  show lift M om Φ.1 (φ ∘ e.symm) (e' h₀ * e' h) = lift M om Φ.1 (φ ∘ e.symm) (e' (h₀ * h))
  rw [map_mul]
end UpperTheory.TP
end
end
