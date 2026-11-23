import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.Growth

section Chg

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (h : ∀ g m, rho g m = rho' g m)

theorem mk_eq_mk_iff (z w : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = Submodule.Quotient.mk w ↔
    ∃ m, ∀ g, z.1 g - w.1 g = rho g m - m := by
  rw [Submodule.Quotient.eq]
  exact mem_coboundaries1 rho _

def chgZ (z : Z1 rho) : Z1 rho' := ⟨z.1, z.2.1, fun g k => by rw [← h]; exact z.2.2 g k⟩

def chg : H1 rho → H1 rho' :=
  Quotient.map' (chgZ rho rho' h) fun z w hzw => by
    obtain ⟨m, hm⟩ := (mk_eq_mk_iff rho z w).1 (Quotient.sound' hzw)
    exact Quotient.exact' ((mk_eq_mk_iff rho' _ _).2 ⟨m, fun g => by rw [← h]; exact hm g⟩)

theorem chg_mk (z : Z1 rho) : chg rho rho' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (chgZ rho rho' h z) := rfl

theorem chg_zero : chg rho rho' h 0 = 0 := rfl

theorem chg_add (x y : H1 rho) : chg rho rho' h (x + y) = chg rho rho' h x + chg rho rho' h y := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  induction y using Submodule.Quotient.induction_on with
  | H w => rfl

theorem chg_smul (a : R) (a' : R') (ha : ∀ m : M, a • m = a' • m) (x : H1 rho) :
    chg rho rho' h (a • x) = a' • chg rho rho' h x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, chg_mk, chg_mk, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => ha _))

theorem chg_mem_span (hs : ∀ a : R, ∃ a' : R', ∀ m : M, a • m = a' • m) {S : Set (H1 rho)} {T : Submodule R' (H1 rho')}
    (hS : ∀ x ∈ S, chg rho rho' h x ∈ T) {x : H1 rho} (hx : x ∈ Submodule.span R S) : chg rho rho' h x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [chg_zero]; exact T.zero_mem
  | add x y _ _ hx hy => rw [chg_add]; exact T.add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨a', ha⟩ := hs a
    rw [chg_smul _ _ _ a a' ha]
    exact T.smul_mem a' hx

theorem chg_chg (x : H1 rho) : chg rho' rho (fun g m => (h g m).symm) (chg rho rho' h x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem res_chg {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (chg rho rho' h x) =
      chg (rho.comp phi) (rho'.comp phi) (fun g m => h (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem chg_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) : chg rho rho' h x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_chg rho rho' h J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (chg_zero _ _ _))

end Chg

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw)

section Sel

variable {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ']
  [Algebra (X.O0 i) Λ'] (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ)
  {B : Type} [AddCommGroup B] [Module Λ B] [Module Λ' B] [TopologicalSpace B] [DiscreteTopology B]
  (h : ∀ g m, repOn ρ κ B g m = repOn ρ κ' B g m) (hs : ∀ a : Λ, ∃ a' : Λ', ∀ b : B, a • b = a' • b)
  (ho : ∀ (y : X.O0 i) (b : B), algebraMap (X.O0 i) Λ y • b = algebraMap (X.O0 i) Λ' y • b)

include hs ho

theorem chg_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) :
    chg _ ((repOn ρ κ' B).comp (DecV N v).subtype) (fun g m => h g.1 m) x ∈ bkOn bkP i ρ κ' B v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · refine chg_mem_span _ _ _ (fun a => (hs a).imp fun a' ha m => funext fun c => ha (m c)) ?_ hx
    rintro x ⟨z, c, y, b, hc, hy, hz, rfl⟩
    exact Submodule.subset_span ⟨chgZ _ _ (fun g m => h g.1 m) z, c, y, b, hc, hy,
      fun g a => (hz g a).trans (ho _ _), rfl⟩
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx]
    exact chg_zero _ _ _

theorem chg_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : chg _ (repOn ρ κ' B) h x ∈ selOn bkP i ρ κ' B Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_chg (repOn ρ κ B) (repOn ρ κ' B) h (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact chg_mem_bkOn bkP i ρ κ κ' h hs ho v _ hv
  · exact Submodule.mem_top
  · exact chg_ur _ _ _ _ _ hv

end Sel

def Represents {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {R : Type} [CommRing R] [Algebra (X.O0 i) R] (κ : GE N →* Rˣ)
    (Q : Finset (PlE D.host)) {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ E : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      (Fin a → B) → H1 (repOn ρ κ B),
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B),
      matAct Ψ u = 0 → E B u ∈ selOn bkP i ρ κ B Q) ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B),
      matAct Ψ u = 0 → matAct Ψ u' = 0 → E B u = E B u' → u = u') ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      ∀ y ∈ selOn bkP i ρ κ B Q, ∃ u, matAct Ψ u = 0 ∧ E B u = y) ∧
    ∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B),
      matAct Ψ u = 0 → E B' (fun c => f (u c)) = h1Map ρ κ f (E B u)

variable {bkP i}

theorem represents_of_computes {s : X.Sig i} {M : ℕ} {ι : Type} {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {Q : Finset (PlE D.host)} {a : ℕ} {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)} (hΦ : Computes bkP i s M d Q Φ)
    {R : Type} [CommRing R] [Algebra (X.O0 i) R] (p : abelian₂ X i M ι →ₐ[X.O0 i] R) (hp : Function.Surjective p)
    (κ : GE N →* Rˣ) (hκ : ∀ g, p (delInv i M d g : (abelian₂ X i M ι)ˣ) = κ g) (n : ℕ) (hn : ((X.l i ^ n : ℕ) : R) = 0) :
    Represents bkP i (Tgl i s) κ Q (Φ.map p) := by
  classical
  obtain ⟨e, he⟩ := hΦ
  have tor : ∀ (B : Type) [AddCommGroup B] [Module R B], ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun B _ _ b =>
    ⟨n, by rw [← Nat.cast_smul_eq_nsmul R, hn, zero_smul]⟩
  let inst : ∀ (B : Type) [AddCommGroup B] [Module R B], Module (abelian₂ X i M ι) B := fun B _ _ =>
    Module.compHom B p.toRingHom
  have hsm : ∀ (B : Type) [AddCommGroup B] [Module R B] (x : abelian₂ X i M ι) (b : B), x • b = p x • b := fun _ _ _ _ _ => rfl
  have hk : ∀ (B : Type) [AddCommGroup B] [Module R B] (u : Fin a → B), matAct (Φ.map p) u = matAct Φ u :=
    fun _ _ _ _ => rfl
  have ho : ∀ (B : Type) [AddCommGroup B] [Module R B] (y : X.O0 i) (b : B),
      algebraMap (X.O0 i) (abelian₂ X i M ι) y • b = algebraMap (X.O0 i) R y • b := fun B _ _ y b => by
    rw [hsm, AlgHom.commutes]
  have hr : ∀ (B : Type) [AddCommGroup B] [Module R B] g m,
      repOn (Tgl i s) (delInv i M d) B g m = repOn (Tgl i s) κ B g m := fun B _ _ g m => by
    funext c
    change (delInv i M d g : abelian₂ X i M ι) • ∑ j, algebraMap (X.O0 i) (abelian₂ X i M ι) _ • m j =
      (κ g : R) • ∑ j, algebraMap (X.O0 i) R _ • m j
    rw [hsm, hκ]
    simp only [ho]
  refine ⟨fun B _ _ _ _ u => if h : matAct Φ u = 0 then chg _ _ (hr B) (e B (tor B) ⟨u, h⟩).1 else 0,
    fun B _ _ _ _ u hu => ?_, fun B _ _ _ _ u u' hu hu' huu => ?_, fun B _ _ _ _ y hy => ?_,
    fun B B' _ _ _ _ _ _ _ _ f u hu => ?_⟩
  · rw [hk] at hu
    simp only [dif_pos hu]
    exact chg_mem_selOn bkP i _ _ _ (hr B) (fun x => ⟨p x, hsm B x⟩) (ho B) Q _ (e B (tor B) ⟨u, hu⟩).2
  · rw [hk] at hu hu'
    simp only [dif_pos hu, dif_pos hu'] at huu
    have h1 := congrArg (chg _ _ fun g m => (hr B g m).symm) huu
    rw [chg_chg, chg_chg] at h1
    exact congrArg Subtype.val ((e B (tor B)).injective (Subtype.ext h1))
  · have h1 := chg_mem_selOn bkP i _ _ _ (fun g m => (hr B g m).symm)
      (fun x => by obtain ⟨x', rfl⟩ := hp x; exact ⟨x', fun b => (hsm B x' b).symm⟩) (fun y b => (ho B y b).symm) Q y hy
    obtain ⟨u, hu⟩ := (e B (tor B)).surjective ⟨_, h1⟩
    have hu0 : matAct Φ u.1 = 0 := u.2
    refine ⟨u.1, hu0, ?_⟩
    simp only [dif_pos hu0]
    rw [show (⟨u.1, hu0⟩ : LinearMap.ker (matAct (M := B) Φ)) = u from rfl, hu]
    exact chg_chg _ _ _ y
  · rw [hk] at hu
    let f' : B →ₗ[abelian₂ X i M ι] B' := ⟨f.toAddHom, fun x b => f.map_smul (p x) b⟩
    have hu' : matAct Φ (fun c => f (u c)) = 0 := by
      show matAct Φ (fun c => f' (u c)) = 0
      funext c
      have := congrArg f' (congrFun hu c)
      simpa [matAct, map_sum] using this
    simp only [dif_pos hu, dif_pos hu']
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B (tor B) ⟨u, hu⟩).1
    rw [he B B' (tor B) (tor B') f' ⟨u, hu⟩ ⟨_, hu'⟩ z (cocycles1MapOfEquivariant _ _ (f'.compLeft _) continuous_of_discreteTopology
      (repOn_map _ _ f') z) (fun _ => rfl) (fun _ _ => rfl) hz.symm, ← hz]
    rfl

end GlobalTheory.Growth
