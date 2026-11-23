import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ClassPtReps
variable {D : D7}

theorem hasMat_iff (h : GA D D.sp.X') (y) :
    GlobalTheory.Core.Rk.Top.HasMat h y ↔ h ∈ GfC D.sp.X' ∧ finM D.sp.X' (Formalism.L2.Forms.rankP D) h = y.1 := by
  have key : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j =
      finM D.sp.X' (Formalism.L2.Forms.rankP D) h (finCongr (Formalism.L2.Forms.rankP D) i) (finCongr (Formalism.L2.Forms.rankP D) j) := by
    intro i j
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Matrix.ext fun i j => ?_⟩
    have := h2 ((finCongr (Formalism.L2.Forms.rankP D)).symm i) ((finCongr (Formalism.L2.Forms.rankP D)).symm j)
    rw [key] at this
    simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j => by rw [key, h2]⟩

theorem nontrivial_finAdeles : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial

theorem inclE_inj : Function.Injective
    (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI := nontrivial_finAdeles (D := D)
  exact Formalism.UG.P.inclE_injective D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem bc_inclE_inj {n : ℕ} : Function.Injective
    (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
      GL (Fin n) D.host.E → GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => inclE_inj (D := D) ?_)
  have h2 := congrArg (fun g : GL (Fin n) _ => g.val i j) hab
  simpa [Formalism.UG.bc] using h2

theorem eq_one_of_GQ {V : HSp D} {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V rfl γ = 1) : γ = 1 := by
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  have h2 : finM V rfl γ = δ.1.map (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl, Matrix.map_map]
    rfl
  have hδ1 : δ.1 = 1 := by
    apply Matrix.map_injective (inclE_inj (D := D))
    beta_reduce
    rw [← h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  apply Subtype.ext
  apply Units.ext
  show mt V γ = 1
  rw [e', hδ1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_GQ' {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V hn γ = 1) : γ = 1 := by
  subst hn
  exact eq_one_of_GQ hγ h1

theorem finGLHom_injOn {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ₁ γ₂ : GA D V} (h1 : γ₁ ∈ GQ V) (h2 : γ₂ ∈ GQ V)
    (e : GlobalTheory.ClassSumLevel.finGLHom V hn γ₁ = GlobalTheory.ClassSumLevel.finGLHom V hn γ₂) : γ₁ = γ₂ := by
  have h3 : γ₁⁻¹ * γ₂ ∈ GQ V := mul_mem (inv_mem h1) h2
  have h4 : finM V hn (γ₁⁻¹ * γ₂) = 1 := by
    have := congrArg Units.val (show GlobalTheory.ClassSumLevel.finGLHom V hn (γ₁⁻¹ * γ₂) = 1 by rw [map_mul, map_inv, e, inv_mul_cancel])
    exact this
  have := eq_one_of_GQ' hn h3 h4
  rw [← mul_inv_cancel_left γ₁ γ₂, this, mul_one]

theorem card_eq_of_lift {G A : Type} [Group G] (H : Subgroup G) (p : G → Prop) (q : A → Prop) (ρ : A → G) (hρ : ∀ a, ρ a ∈ H)
    (hpq : ∀ a, p (ρ a) ↔ q a) (hi : ∀ a b, ρ a = ρ b → a = b) (hs : ∀ γ ∈ H, ∃ a, ρ a = γ) :
    Nat.card {γ : H // p γ.1} = Nat.card {a // q a} := by
  refine (Nat.card_eq_of_bijective (fun a : {a // q a} => (⟨⟨ρ a.1, hρ a.1⟩, (hpq _).2 a.2⟩ : {γ : H // p γ.1}))
    ⟨fun a b hab => Subtype.ext (hi _ _ (congrArg (fun x : {γ : H // p γ.1} => x.1.1) hab)), fun γ => ?_⟩).symm
  obtain ⟨a, ha⟩ := hs γ.1.1 γ.1.2
  exact ⟨⟨a, (hpq a).1 (ha ▸ γ.2)⟩, Subtype.ext (Subtype.ext ha)⟩

open scoped ComplexOrder in
set_option maxHeartbeats 2000000 in

theorem isReps_of_level (V : HSp D) {n : ℕ} (hn : V.rank = n) (hV : ∀ τ, (gramAt D V τ).PosDef) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → Formalism.UG.UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (h : cl → GA D V) (hf : ∀ c, h c ∈ GfC V)
    (hh : ∀ c, finM V hn (h c) = (yc c).1.1) (U : Subgroup (GA D V))
    (mem : ∀ x, x ∈ U ↔ x ∈ GfC V ∧ x ∈ GlobalTheory.ClassSumLevel.levG V hn S) :
    IsReps V U h ∧ ∀ c, stabOrd U (h c) = Nat.card {δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)) //
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 ∈
        S.U.map (MulAut.conj (yc c).1).toMonoidHom} := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.1
  haveI := hT.2.2.2.2.1
  have hinf : ∀ k ∈ GinfC V, k ∈ GlobalTheory.ClassSumLevel.levG V hn S := fun k hk =>
    ⟨1, (GlobalTheory.ClassSumLevel.finM_eq_one_of_mem_GinfC V hn hk).symm⟩
  have split : ∀ k ∈ GlobalTheory.ClassSumLevel.levG V hn S, ∃ a ∈ GinfC V, ∃ κ ∈ U, k = a * κ := by
    intro k hk
    obtain ⟨a, ha, κ, hκ, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
    refine ⟨a, ha, κ, (mem κ).2 ⟨hκ, ?_⟩, rfl⟩
    have := mul_mem (inv_mem (hinf a ha)) hk
    rwa [inv_mul_cancel_left] at this
  have hex := GlobalTheory.ClassSumLevel.existsUnique_class V hn S yc hy h hh
  refine ⟨⟨fun x hx => ((mem x).1 hx).1, ?_, ?_, hf, fun g => ?_, fun c c' γ hγ k hk κ hκ e => ?_⟩, fun c => ?_⟩
  · have hc := GlobalTheory.ClassSumLevel.isCompact_levG V hn S hV
    have hcl : IsClosed (GfC V : Set (GA D V)) := by
      have e : (GfC V : Set (GA D V)) = {g | ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g} := by
        ext g
        exact ⟨fun hg => congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (V := V) ⟨g, hg⟩), fun hg => by
          have hg' : ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g := hg
          rw [← hg']
          exact (GlobalTheory.AutMult.toFin V g).2⟩
      rw [e]
      exact isClosed_eq (continuous_subtype_val.comp (GlobalTheory.AutMult.continuous_toFin V)) continuous_id
    have e : (U : Set (GA D V)) = (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) ∩ (GfC V : Set (GA D V)) :=
      Set.ext fun x => (mem x).trans and_comm
    rw [e]
    exact hc.inter_right hcl
  · have e : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) :=
      Set.ext fun x => ⟨fun hx => ((mem x.1).1 (Subgroup.mem_subgroupOf.1 hx)).2,
        fun hx => Subgroup.mem_subgroupOf.2 ((mem x.1).2 ⟨x.2, hx⟩)⟩
    rw [e]
    exact (GlobalTheory.ClassSumLevel.isOpen_levG V hn S).preimage continuous_subtype_val
  · obtain ⟨c, ⟨γ, hγ, k, hk, e⟩, -⟩ := hex g
    obtain ⟨a, ha, κ, hκ, rfl⟩ := split k hk
    exact ⟨γ, hγ, c, a, ha, κ, hκ, by rw [e]; simp only [mul_assoc]⟩
  · obtain ⟨c₀, -, hu⟩ := hex (h c')
    have h1 := hu c ⟨γ, hγ, k * κ, mul_mem (hinf k hk) ((mem κ).1 hκ).2, by rw [e]; simp only [mul_assoc]⟩
    have h2 := hu c' ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩
    exact h1.trans h2.symm
  · have hh' : GlobalTheory.ClassSumLevel.finGLHom V hn (h c) = (yc c).1 := Units.ext (hh c)
    have key : ∀ γ : GA D V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔
        GlobalTheory.ClassSumLevel.finGLHom V hn γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom := by
      intro γ
      have e1 : (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔ (h c)⁻¹ * γ * h c ∈ GlobalTheory.ClassSumLevel.levG V hn S := by
        constructor
        · rintro ⟨k, hk, κ, hκ, e⟩
          rw [mul_assoc, e, mul_assoc, inv_mul_cancel_left]
          exact mul_mem (hinf k hk) ((mem κ).1 hκ).2
        · intro hz
          obtain ⟨a, ha, κ, hκ, e⟩ := split _ hz
          exact ⟨a, ha, κ, hκ, by rw [mul_assoc, ← e, mul_assoc, mul_inv_cancel_left]⟩
      rw [e1, GlobalTheory.ClassSumLevel.mem_levG_iff, map_mul, map_mul, map_inv, hh']
      constructor
      · intro hz
        refine ⟨_, hz, ?_⟩
        show (yc c).1 * _ * (yc c).1⁻¹ = _
        group
      · rintro ⟨κ, hκ, e⟩
        have e' : (yc c).1 * κ * (yc c).1⁻¹ = GlobalTheory.ClassSumLevel.finGLHom V hn γ := e
        rw [← e', show (yc c).1⁻¹ * ((yc c).1 * κ * (yc c).1⁻¹) * (yc c).1 = κ by group]
        exact hκ
    have hr : ∀ δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)), ∃ γ ∈ GQ V,
        GlobalTheory.ClassSumLevel.finGLHom V hn γ =
          Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 := fun δ =>
      GlobalTheory.ClassSumLevel.exists_GQ_of_mem_ratPts V hn ⟨δ.1, δ.2, rfl⟩
    choose ρ hρ eρ using hr
    unfold stabOrd
    refine card_eq_of_lift (GQ V) (fun γ => ∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) _ ρ hρ (fun δ => (key _).trans (by rw [eρ])) (fun a b e => ?_) fun γ hγ => ?_
    · exact Subtype.ext (bc_inclE_inj (D := D) ((eρ a).symm.trans ((congrArg _ e).trans (eρ b))))
    · obtain ⟨δ, hδ, e⟩ := GlobalTheory.ClassSumLevel.finGLHom_mem_ratPts V hn hγ
      exact ⟨⟨δ, hδ⟩, finGLHom_injOn hn (hρ ⟨δ, hδ⟩) hγ ((eρ ⟨δ, hδ⟩).trans e)⟩

set_option maxHeartbeats 1000000 in

theorem isReps_stabOrd_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J _ j _ _ P t r a k tl Ch₀ A ι w _ UT ε hpin bad K eW _ _ _ hLev _ h hh
  have mem : ∀ x, x ∈ UT ↔ x ∈ GfC (I.rec7 l Z).sp.X' ∧
      x ∈ GlobalTheory.ClassSumLevel.levG (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z)) K.lev := by
    intro x
    refine ((hpin.lev x).trans (hLev.1 x)).trans ⟨?_, ?_⟩
    · rintro ⟨κ, hκ⟩
      exact ⟨hκ.1, κ, ((hasMat_iff x _).1 hκ).2.symm⟩
    · rintro ⟨h1, κ, hκ⟩
      exact ⟨κ, (hasMat_iff x _).2 ⟨h1, hκ.symm⟩⟩
  have H := isReps_of_level (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z))
    (GlobalTheory.RepsObj.gramAt_posDef (D7.X'_posDef _) (I.rec7 l Z).sp.X'_sig) K.lev K.y K.y_bij h (fun c => (hh c).1)
    (fun c => ((hasMat_iff _ _).1 (hh c)).2) UT mem
  refine ⟨H.1, fun c => (H.2 c).trans ?_⟩
  exact (Nat.card_congr ((MonoidHom.ofInjective (K.stabI_inj c)).toEquiv.trans
    (Equiv.subtypeEquivRight (K.stabI_range c)))).symm

end GlobalTheory.ClassPtReps
