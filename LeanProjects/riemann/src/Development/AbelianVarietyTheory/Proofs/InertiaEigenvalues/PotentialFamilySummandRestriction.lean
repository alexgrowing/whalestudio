import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankEqOfNondegenerate
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDual

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isDR_of_summand (D : D7) (hFont : FontaineAtPlacesOverL (D := D)) (hP : PotDRL D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ)
    (hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n)
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) : IsDR (Br.PD D.loc D.nbr i w hw) X.ρ := by
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W'.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X hW'

section Lin

variable {LL : Type} [Field LL] {a n : ℕ}

def pr (LL : Type) [Field LL] (a n : ℕ) :
    (Fin a → Fin n → LL) →ₗ[LL] (Fin a → Fin n → LL) →ₗ[LL] LL :=
  LinearMap.mk₂ LL (fun u u' => ∑ b, u b ⬝ᵥ u' b)
    (fun u₁ u₂ u' => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun c u u' => by simp [smul_dotProduct, Finset.mul_sum])
    (fun u u₁ u₂ => by simp [dotProduct_add, Finset.sum_add_distrib])
    (fun c u u' => by simp [dotProduct_smul, Finset.mul_sum])

theorem pr_apply (u u' : Fin a → Fin n → LL) : pr LL a n u u' = ∑ b, u b ⬝ᵥ u' b := rfl

def ann (C : Submodule LL (Fin a → Fin n → LL)) : Submodule LL (Fin a → Fin n → LL) where
  carrier := {u' | ∀ u ∈ C, pr LL a n u u' = 0}
  add_mem' := fun h1 h2 u hu => by rw [map_add, h1 u hu, h2 u hu, add_zero]
  zero_mem' := fun u _ => by rw [map_zero]
  smul_mem' := fun c u' h u hu => by rw [map_smul, h u hu, smul_zero]

theorem pr_single (b : Fin a) (k : Fin n) (u' : Fin a → Fin n → LL) :
    pr LL a n (Pi.single b (Pi.single k 1)) u' = u' b k := by
  rw [pr_apply, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem exists_rep (φ : (Fin a → Fin n → LL) →ₗ[LL] LL) :
    ∃ u' : Fin a → Fin n → LL, ∀ u, φ u = pr LL a n u u' := by
  refine ⟨fun b k => φ (Pi.single b (Pi.single k 1)), fun u => ?_⟩
  have hu : u = ∑ b, ∑ k, u b k • (Pi.single b (Pi.single k 1) : Fin a → Fin n → LL) := by
    funext b' k'
    simp [Finset.sum_apply, Pi.single_apply, ite_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
  conv_lhs => rw [hu]
  rw [pr_apply]
  simp [map_sum, dotProduct]

theorem eq_zero_of_pr (u' : Fin a → Fin n → LL) (h : ∀ u, pr LL a n u u' = 0) : u' = 0 := by
  funext b k
  rw [← pr_single b k u']
  exact h _

end Lin

section Lin2

variable {LL : Type} [Field LL] {a n : ℕ}

theorem left_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u : Fin a → Fin n → LL)
    (hu : u ∈ R) (h : ∀ u' ∈ ann C, pr LL a n u u' = 0) : u = 0 := by
  by_contra hne
  have hne' : (⟨u, hu⟩ : ↥R) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual LL ↥R, f ⟨u, hu⟩ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne' ((Module.forall_dual_apply_eq_zero_iff LL _).1 hall)
  obtain ⟨u', hu'⟩ := exists_rep (f ∘ₗ R.projectionOnto C hRC)
  have hann : u' ∈ ann C := by
    intro c hc
    rw [← hu', LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_right' hRC hc, map_zero]
  apply hf
  have := hu' u
  rw [LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_left hRC ⟨u, hu⟩] at this
  rw [this]
  exact h u' hann

theorem right_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) (h : ∀ u ∈ R, pr LL a n u u' = 0) : u' = 0 := by
  apply eq_zero_of_pr
  intro u
  have hu : u ∈ R ⊔ C := by rw [hRC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add, LinearMap.add_apply, h y hy, hu' z hz, add_zero]

variable {G : Type} [Group G] (T U : Fin a → (G →* Matrix (Fin n) (Fin n) LL)) (χ : G → LL)

theorem pr_equiv (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (g : G) (u u' : Fin a → Fin n → LL) :
    pr LL a n (fun b => (T b g).mulVec (u b)) (fun b => (U b g).mulVec (u' b)) = χ g * pr LL a n u u' := by
  rw [pr_apply, pr_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
    dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
    inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem ann_stable (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (C : Submodule LL (Fin a → Fin n → LL))
    (hC : ∀ g, ∀ u ∈ C, (fun b => (T b g).mulVec (u b)) ∈ C) (g : G) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) : (fun b => (U b g).mulVec (u' b)) ∈ ann C := by
  intro u hu
  have e : u = fun b => (T b g).mulVec ((T b g⁻¹).mulVec (u b)) := by
    funext b
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  rw [e, pr_equiv T U χ hU, hu' _ (hC g⁻¹ u hu), mul_zero]

end Lin2

theorem finrank_eq_of_perfect {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    finrank LL V = finrank LL V' := by
  first
  | exact @_root_.GlobalTheory.NondegenerateFinrank.main
  | exact _root_.GlobalTheory.NondegenerateFinrank.main
  | (apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NondegenerateFinrank.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NondegenerateFinrank.main ..)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dual_of_summand (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) :
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  obtain ⟨a, x, j, hjinj, hjeq, C, hC, hcompl⟩ := hX
  let Ms : ↥Xs → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => Br.loc D.nbr i w hw (rDuO D.nd i r y)
  have hc : ∀ y v, Continuous fun g => (Ms y g).mulVec v := fun y v =>
    (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).2).matrix_mulVec continuous_const
  let T : Fin a → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun b => Br.loc D.nbr i w hw (rTwO D.nd i r (x b))
  let χ : Br.G D.nbr i w hw → Br.LL D.nbr i w hw := fun g =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw)
  have hU : ∀ b g, Ms (x b) g = χ g • (T b g⁻¹).transpose := fun b g =>
    GlobalTheory.JumpDual.loc_dual D i w hw r (x b) g
  let A := GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) Ms hc x
  have hstab : ∀ g, ∀ u ∈ ann C, A.ρ g u ∈ ann C := fun g u hu =>
    ann_stable T (fun b => Ms (x b)) χ hU C hC g u hu
  let X' := A.sub (ann C) hstab
  let PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw :=
    (pr (Br.LL D.nbr i w hw) a D.R.nV).compl₁₂ j (ann C).subtype
  have hPX : ∀ v (y : X'.V), PX v y = pr (Br.LL D.nbr i w hw) a D.R.nV (j v) ((ann C).subtype y) :=
    fun _ _ => rfl
  have h2 : ∀ v, (∀ y, PX v y = 0) → v = 0 := by
    intro v h
    apply hjinj
    rw [map_zero]
    exact left_nondeg (LinearMap.range j) C hcompl (j v) ⟨v, rfl⟩ fun u' hu' => h ⟨u', hu'⟩
  have h3 : ∀ y, (∀ v, PX v y = 0) → y = 0 := by
    intro y h
    apply Subtype.ext
    exact right_nondeg (LinearMap.range j) C hcompl y.1 y.2 (by
      rintro u ⟨v, rfl⟩
      exact h v)
  refine ⟨X', PX, ⟨fun g v y => ?_, h2, h3, finrank_eq_of_perfect PX h2 h3⟩, ?_⟩
  · rw [hPX, hPX, hjeq]
    exact pr_equiv T (fun b => Ms (x b)) χ hU g (j v) ((ann C).subtype y)
  · refine ⟨a, x, fun b => LinearMap.proj b ∘ₗ (ann C).subtype, fun b g v => rfl, fun v hv => ?_⟩
    exact Subtype.ext (funext hv)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem xdual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
      IsDR (Br.PD D.loc D.nbr i w hw) X.ρ ∧
      ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  intro D hFont hP i r hr Xs w hw n hPot X hX
  exact ⟨isDR_of_summand D hFont hP i r hr Xs w hw n hPot X hX, dual_of_summand D i r hr Xs w hw X hX⟩

end GlobalTheory.SummandDual

end
