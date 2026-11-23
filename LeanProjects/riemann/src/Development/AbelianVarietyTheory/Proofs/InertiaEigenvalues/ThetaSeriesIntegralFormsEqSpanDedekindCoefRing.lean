import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.FormsBaseChange

section Algebra

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {R O : Subring ℂ}

def Indep (M : Submodule R W) : Prop :=
  ∀ (I : Type) (f : I → W), (∀ a, f a ∈ M) → LinearIndependent R f → LinearIndependent ℂ f

theorem exists_extend {N : Submodule R W} (hN : Indep N) (s : N →ₗ[R] V) : ∃ s' : W →ₗ[ℂ] V, ∀ n : N, s' n = s n := by
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn R (fun n : N => n)
  have h1 : LinearIndependent ℂ fun a : I => ((a.1 : N) : W) :=
    hN I _ (fun a => a.1.2) (LinearIndependent.map' hI N.subtype N.ker_subtype)
  obtain ⟨s', hs'⟩ := LinearMap.exists_extend ((Module.Basis.span h1).constr ℂ fun a : I => s a.1)
  have h2 : ∀ a : I, s' (a.1 : W) = s a.1 := fun a => by
    have := LinearMap.congr_fun hs' (Module.Basis.span h1 a)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at this
    exact this
  have h3 : ∀ n ∈ Submodule.span R ((fun n : N => n) '' I), s' (n : W) = s n := fun n hn => by
    induction hn using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact h2 ⟨a, ha⟩
    | zero => simp
    | add _ _ _ _ e1 e2 => rw [Submodule.coe_add, map_add, map_add, e1, e2]
    | smul a x _ e =>
      rw [map_smul, ← e]
      exact s'.map_smul (a : ℂ) (x : W)
  refine ⟨s', fun n => ?_⟩
  by_cases hn : n ∈ I
  · exact h2 ⟨n, hn⟩
  obtain ⟨a, ha, h⟩ := hmax n hn
  have h4 : (a : ℂ) • s' (n : W) = (a : ℂ) • s n := by
    rw [← map_smul]
    exact (h3 _ h).trans (map_smul s a n)
  exact smul_right_injective V (fun e => ha (Subtype.ext e)) h4

theorem mem_span_ker [IsDedekindDomain R] {L : Submodule R V} (hL : L.FG) {M : Submodule R W} (hM : Indep M) (T : V →ₗ[ℂ] W)
    (hT : ∀ x ∈ L, T x ∈ M) {x : V} (hx : x ∈ Submodule.span O (L : Set V)) (h0 : T x = 0) :
    x ∈ Submodule.span O ((L ⊓ (LinearMap.ker T).restrictScalars R : Submodule R V) : Set V) := by
  let t : V →ₗ[R] W := T.restrictScalars R
  let N : Submodule R W := L.map t
  have hN : Indep N := fun I f hf => hM I f fun a => by
    obtain ⟨y, hy, e⟩ := hf a
    exact e ▸ hT y hy
  haveI : Module.Finite R N := Module.Finite.iff_fg.2 (hL.map t)
  haveI : Module.Flat R N := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro n ⟨a, ha⟩
    have h1 : ((a.1 : R) : ℂ) • (n : W) = 0 := congrArg Subtype.val ha
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left fun e => nonZeroDivisors.coe_ne_zero a (Subtype.ext e))
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  haveI : Module.Projective R N := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (t.submoduleMap L) (LinearMap.id : N →ₗ[R] N) (t.submoduleMap_surjective L)
  obtain ⟨s', hs'⟩ := exists_extend hN (L.subtype ∘ₗ s)
  have e : x = x - s' (T x) := by rw [h0, map_zero, sub_zero]
  rw [e]
  clear e h0
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have h1 := hs' ⟨T y, y, hy, rfl⟩
    have h2 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨T y, y, hy, rfl⟩)
    refine Submodule.subset_span ⟨?_, ?_⟩
    · rw [h1]
      exact sub_mem hy (s _).2
    · change T _ = 0
      rw [map_sub, h1]
      exact sub_eq_zero.2 h2.symm
  | zero => simp
  | add y z _ _ h1 h2 =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem h1 h2
  | smul a y _ h1 =>
    have := Submodule.smul_mem _ a h1
    rw [smul_sub] at this
    change (a : ℂ) • y - s' (T ((a : ℂ) • y)) ∈ _
    rw [map_smul, map_smul]
    exact this

theorem mem_span_iInf_ker [IsDedekindDomain R] {M : Submodule R W} (hM : Indep M) {A : Type} (T : A → V →ₗ[ℂ] W) (n : ℕ) :
    ∀ L : Submodule R V, L.FG → Module.finrank ℂ (Submodule.span ℂ (L : Set V)) = n → (∀ a, ∀ x ∈ L, T a x ∈ M) →
      ∀ x ∈ Submodule.span O (L : Set V), (∀ a, T a x = 0) → x ∈ Submodule.span O {y | y ∈ L ∧ ∀ a, T a y = 0} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL hn hT x hx h0
    by_cases h : ∀ a, ∀ y ∈ L, T a y = 0
    · exact Submodule.span_mono (fun y hy => And.intro hy fun a => h a y hy) hx
    push Not at h
    obtain ⟨a, y, hy, hy0⟩ := h
    let L' : Submodule R V := L ⊓ (LinearMap.ker (T a)).restrictScalars R
    have hL' : L'.FG := hL.of_le inf_le_left
    haveI : Module.Finite ℂ (Submodule.span ℂ (L : Set V)) := by
      obtain ⟨s, rfl⟩ := hL
      rw [Submodule.span_span_of_tower]
      exact Module.Finite.span_finset ℂ s
    have hlt : Submodule.span ℂ (L' : Set V) < Submodule.span ℂ (L : Set V) := by
      refine lt_of_le_of_ne (Submodule.span_mono fun z hz => hz.1) fun e => hy0 ?_
      have h1 : Submodule.span ℂ (L' : Set V) ≤ LinearMap.ker (T a) := Submodule.span_le.2 fun z hz => hz.2
      exact h1 (e ▸ Submodule.subset_span hy)
    have := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) L' hL' rfl (fun b z hz => hT b z hz.1) x
      (mem_span_ker hL hM (T a) (hT a) hx (h0 a)) h0
    exact Submodule.span_mono (fun z hz => And.intro hz.1.1 hz.2) this

theorem law_mem_span [IsDedekindDomain R] {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W)
    (J : Subgroup G) (χ : J →* ℂˣ) (hχ : ∀ k, ((χ k : ℂˣ) : ℂ) ∈ R) (C : G → Submodule R W) (hfg : ∀ g, (C g).FG)
    (hact : ∀ (γ : Γ) (g : G) (k : J), ∀ P ∈ C g, ρ γ P ∈ C (ι γ * g * k)) (hM : Indep (Submodule.pi Set.univ C))
    {I : Type} [Finite I] (y : I → G) (hy : ∀ g, ∃ (c : I) (γ : Γ) (k : J), g = ι γ * y c * k) {f : G → W}
    (hf : f ∈ lawForms ι ρ J χ) (hv : ∀ g, f g ∈ Submodule.span O (C g : Set W)) :
    f ∈ Submodule.span O {F | F ∈ lawForms ι ρ J χ ∧ ∀ g, F g ∈ C g} := by
  classical
  choose c γ k hg using hy
  let E : (I → W) →ₗ[ℂ] (G → W) := LinearMap.pi fun g => ((χ (k g) : ℂˣ) : ℂ) • (ρ (γ g) ∘ₗ LinearMap.proj (c g))
  have hE : ∀ v g, E v g = ((χ (k g) : ℂˣ) : ℂ) • ρ (γ g) (v (c g)) := fun _ _ => rfl
  let L : Submodule R (I → W) := Submodule.pi Set.univ fun i => C (y i)
  have hL : L.FG := Submodule.fg_pi fun i => hfg (y i)
  have hEL : ∀ v ∈ L, ∀ g, E v g ∈ C g := fun v hv g => by
    have := hact (γ g) _ (k g) _ (hv (c g) trivial)
    rw [← hg g] at this
    exact (C g).smul_mem (⟨_, hχ (k g)⟩ : R) this
  let T : Γ × J → (I → W) →ₗ[ℂ] (G → W) := fun a =>
    E - (LinearMap.pi fun g => ((χ a.2 : ℂˣ) : ℂ) • (ρ a.1 ∘ₗ LinearMap.proj ((ι a.1)⁻¹ * g * (a.2 : G)⁻¹))) ∘ₗ E
  have hT : ∀ a v g, T a v g = E v g - ((χ a.2 : ℂˣ) : ℂ) • ρ a.1 (E v ((ι a.1)⁻¹ * g * (a.2 : G)⁻¹)) := fun _ _ _ => rfl
  have hc : ∀ (a : Γ × J) g, ι a.1 * ((ι a.1)⁻¹ * g * (a.2 : G)⁻¹) * a.2 = g := fun a g => by group
  have hTL : ∀ a, ∀ v ∈ L, T a v ∈ Submodule.pi Set.univ C := fun a v hv g _ => by
    rw [hT]
    have := hact a.1 _ a.2 _ (hEL v hv ((ι a.1)⁻¹ * g * (a.2 : G)⁻¹))
    rw [hc] at this
    exact sub_mem (hEL v hv g) ((C g).smul_mem (⟨_, hχ a.2⟩ : R) this)
  have hEf : E (fun i => f (y i)) = f := funext fun g => by
    rw [hE, ← mem_lawForms.1 hf, ← hg g]
  have hx : (fun i => f (y i)) ∈ Submodule.span O (L : Set (I → W)) := by
    haveI := Fintype.ofFinite I
    rw [← Finset.univ_sum_single (fun i => f (y i))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : I => W) i) (hv (y i))
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨P, hP, rfl⟩ j _
    by_cases e : j = i
    · subst e
      simpa using hP
    · simp [e]
  have h1 := mem_span_iInf_ker (O := O) hM T _ L hL rfl hTL _ hx fun a => funext fun g => by
    rw [hT, hEf, ← mem_lawForms.1 hf, hc, sub_self]
    rfl
  have h2 := Submodule.mem_map_of_mem (f := E.restrictScalars O) h1
  rw [Submodule.map_span, LinearMap.restrictScalars_apply, hEf] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, ⟨hvL, hv0⟩, rfl⟩
  refine ⟨mem_lawForms.2 fun a g b => ?_, hEL v hvL⟩
  have := congrFun (hv0 (a, b)) (ι a * g * b)
  rw [hT, show (ι a)⁻¹ * (ι a * g * b) * (b : G)⁻¹ = g by group] at this
  exact sub_eq_zero.1 this

theorem indep_closure {I : Type} {f : I → W} (h : LinearIndependent R f) :
    LinearIndependent (Subfield.closure (R : Set ℂ)) f := by
  letI : Algebra R (Subfield.closure (R : Set ℂ)) :=
    (Subring.inclusion (S := R) (T := (Subfield.closure (R : Set ℂ)).toSubring) Subfield.subset_closure).toAlgebra
  haveI : IsScalarTower R (Subfield.closure (R : Set ℂ)) W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : FaithfulSMul R (Subfield.closure (R : Set ℂ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Subring.inclusion_injective _)
  haveI : IsFractionRing R (Subfield.closure (R : Set ℂ)) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, e⟩ := Subfield.mem_closure_iff.1 z.2
    rw [Subring.closure_eq] at ha hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext e.symm⟩
  exact (LinearIndependent.iff_fractionRing R _).1 h

end Algebra

variable {D : D7} {S T : HSp D} {B : Base S T} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
  {emb : D.what₂.Tau → (D.host.E →+* K)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ T.rank := by
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

theorem coefLat_le_span (hB : B.Good) (R O : Subring ℂ) (h : Bridge.Gf S) {P : PolF D T.rank S.rank}
    (hP : P ∈ B.coefLat σ emb O h) : P ∈ Submodule.span O (B.coefLat σ emb R h : Set (PolF D T.rank S.rank)) := by
  have hle : Submodule.span O (B.coefLat σ emb R h : Set (PolF D T.rank S.rank)) ≤
      (harm T.rank B.w B.F.BS).restrictScalars O := Submodule.span_le.2 fun x hx => hx.1
  have h1 : coefLatFn σ emb O B.w.lam (B.latAt h) ≤
      (Submodule.span O (B.coefLat σ emb R h : Set (PolF D T.rank S.rank))).map
        ((harmFn T.rank B.w B.F.BS).restrictScalars O) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have h2 : coefFn σ B.w.lam (F : VV K B.w.lam) ∈ (harm T.rank B.w B.F.BS).map (harmFn T.rank B.w B.F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB)]
      exact Submodule.subset_span ⟨_, HarmLattice.coefFn_eq σ B.w.lam F⟩
    obtain ⟨Q, hQ, e⟩ := h2
    refine ⟨Q, Submodule.subset_span ((mem_harmLat _ _ _).2 ⟨hQ, ?_⟩), e⟩
    rw [e]
    exact Submodule.subset_span ⟨F, hF, rfl⟩
  obtain ⟨Q, hQ, e⟩ := h1 hP.2
  have h0 : P - Q = 0 := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem hP.1 (hle hQ))
    (by rw [map_sub]; exact sub_eq_zero.2 e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem mtLat_eq_span : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ ψ : Twist D Circle, ψ.Good → B.admitted ψ.Q → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (R : Type) [CommRing R] [IsDedekindDomain R] (φ : R →+* ℂ), Function.Injective φ → IsCoefRing σ emb φ.range →
  (∀ k : B.levJ ψ, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ φ.range) → ∀ O : Subring ℂ, φ.range ≤ O →
  B.mtLat σ emb O ψ = Submodule.span O (B.mtLat σ emb φ.range ψ : Set (Bridge.Gf S → PolF D T.rank S.rank)) := by
  intro D S T B hB ψ _ _ K _ _ σ emb R _ _ φ hφ hc hlam O hO
  haveI : IsDedekindDomain φ.range := by
    letI : Algebra R φ.range := φ.rangeRestrict.toAlgebra
    haveI : IsLocalization (⊥ : Submonoid R) φ.range :=
      IsLocalization.of_le_isUnit_of_bijective (by rintro _ ⟨x, hx, rfl⟩; rw [Submonoid.mem_bot.1 hx, map_one]; exact one_mem _)
        ⟨fun _ _ e => hφ (congrArg Subtype.val e), φ.rangeRestrict_surjective⟩
    exact IsLocalization.isDedekindDomain R (M := ⊥) bot_le _
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 fun f hf => ?_)
  · obtain ⟨m, y, hy⟩ := exists_isClassSystem B hB.frame ψ
    obtain ⟨h1, h2⟩ := (B.mem_mtLat σ emb O).1 hf
    have := law_mem_span (O := O) (Bridge.ratF S) (B.act.comp (GQ S).subtype) (B.levJ ψ) (B.levLam ψ) hlam
      (B.coefLat σ emb φ.range)
      (fun g => (HarmLattice.harmLat_fg_span D _ _ _ _ _ _ _ _ _ hB.wt (pq_le hB) hc
        (Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg) hB.frame.sdS.1.span_eq_top _)).1)
      (fun γ g k P hP => Base.act_mem_coefLat hB.frame hc γ g k (Base.mem_St_of_mem_levJ k.2) hP)
      (fun I F hF hi => GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice D S T B hB K σ emb φ.range hc (Subfield.closure (φ.range : Set ℂ)) Subfield.subset_closure I F
        (fun a g => hF a g trivial) (indep_closure hi))
      (fun i => finPt S (y i)) (fun g => by
        obtain ⟨c, ⟨γ, k, e⟩, -⟩ := hy.reps g
        exact ⟨c, γ, k, e⟩) h1.2 (fun g => coefLat_le_span hB φ.range O g (h2 g))
    refine Submodule.span_mono ?_ this
    rintro F ⟨hF1, hF2⟩
    exact (B.mem_mtLat σ emb φ.range).2 ⟨⟨fun g _ => (hF2 g).1, hF1⟩, hF2⟩
  · obtain ⟨h1, h2⟩ := (B.mem_mtLat σ emb φ.range).1 hf
    refine (B.mem_mtLat σ emb O).2 ⟨h1, fun g => (mem_harmLat _ _ _).2 ⟨(h2 g).1, ?_⟩⟩
    have key : ∀ x ∈ coefLatFn σ emb φ.range B.w.lam (B.latAt g), x ∈ coefLatFn σ emb O B.w.lam (B.latAt g) := fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span h
      | zero => exact zero_mem _
      | add _ _ _ _ e1 e2 => exact add_mem e1 e2
      | smul a x _ e => exact Submodule.smul_mem _ (⟨a.1, hO a.2⟩ : O) e
    exact key _ (h2 g).2

end GlobalTheory.FormsBaseChange

end
