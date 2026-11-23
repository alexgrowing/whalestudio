import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GraphOfFixedGraph
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraphStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPlaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperatorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilatorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIso

section Abstract

variable {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : G →* Module.End ℂ V} {Gv Gc : ι → Subgroup G}
  {J : Subgroup G}

theorem graph_of_local' (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  obtain ⟨X, hX0, hXm, hX, i₁, i₂⟩ := GlobalTheory.T.exists_stable_graph_of_equal_annihilators V ι (fun v => locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J)
    (fixIn ρ J S₁) (fixIn ρ J S₂) hfd n₁ n₂
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₁.stab hx.1, hc.2 x hx.2⟩)
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₂.stab hx.1, hc.2 x hx.2⟩)
    (fun v w hvw c hc d hd => ⟨fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x,
      fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x⟩)
    (fun v c hc => by
      obtain ⟨P, hP⟩ := exists_avg ρ (Gv v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨Q, hQ⟩ := exists_avg ρ (Gc v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₁ h₂ n₁ hX hc.1,
        ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₂ h₁ n₂ hX.swap hc.1⟩)
    (fun Y hY hst => fixIn_simple H horb h₁ Y hY hst) (fun Y hY hst => fixIn_simple H horb h₂ Y hY hst)
  exact graph_of_fixed_graph H horb h₁ h₂ n₁ n₂ X hX0 hXm hX i₁ i₂

theorem graph_of_local (H : PlaceSys Gv Gc J) {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂)
    (horb : ∀ x ∈ S₁ ⊔ S₂, ((fun k => ρ k x) '' (J : Set G)).Finite)
    (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  have hne : ∀ S ≤ S₁ ⊔ S₂, fixIn ρ J S ≠ ⊥ →
      fixIn (res ρ _ (sup_stab h₁ h₂)) J (S.comap (S₁ ⊔ S₂).subtype) ≠ ⊥ := by
    intro S hS h
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact (Submodule.ne_bot_iff _).2 ⟨⟨f, hS hf.1⟩, ⟨hf.1, fun k hk => Subtype.ext (hf.2 k hk)⟩,
      fun e => hf0 (congrArg Subtype.val e)⟩
  obtain ⟨W, hW⟩ := graph_of_local' (ρ := res ρ _ (sup_stab h₁ h₂)) H (orbit_res horb) (h₁.res le_sup_left)
    (h₂.res le_sup_right) (hne _ le_sup_left n₁) (hne _ le_sup_right n₂)
    (FiniteDimensional.of_injective
      (((S₁ ⊔ S₂).subtype.comp (fixIn (res ρ _ (sup_stab h₁ h₂)) J (S₁.comap (S₁ ⊔ S₂).subtype)).subtype).codRestrict
        (fixIn ρ J S₁) (fun f => ⟨f.2.1, fun k hk => congrArg Subtype.val (f.2.2 k hk)⟩))
      (fun a b e => by
        have e' := congrArg Subtype.val e
        exact Subtype.ext (Subtype.ext e')))
    (fun v => by
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨_, hX.res le_sup_left le_sup_right⟩)
  exact ⟨_, hW.of_res⟩

end Abstract

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def rtRep (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun g := NG.rt L n g
  map_one' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * 1) = φ x
    rw [mul_one]
  map_mul' g g' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * (g * g')) = φ (x * g * g')
    rw [mul_assoc]

def Gaway (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v}ᶜ x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := GlobalTheory.InertSph.trivOutside_one _
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

theorem placeSys {N : ℕ} (hN : 0 < N) :
    PlaceSys (GlobalTheory.InertSph.Gv L n) (Gaway L n) (GlobalTheory.IsotOrth.congSub L n N) where
  comm := fun v x hx y hy => (GlobalTheory.InertSph.commute_of_trivOutside v x y hx hy).eq
  le := fun v w hvw x hx u hu => hx u (by
    have : u = v := by simpa using hu
    subst this
    simpa using hvw)
  dec := fun v g => by
    obtain ⟨x, y, hx, hy, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, y, hy, e⟩
  decJ := fun v k hk => by
    obtain ⟨x, y, hx, hy, cx, cy, e⟩ := GlobalTheory.T.principalCongruence_split_trivOutside_and_at_place L n N v k hk
    exact ⟨x, ⟨hx, cx⟩, y, ⟨hy, cy⟩, e⟩
  ind := fun p h1 h2 => GlobalTheory.T.finiteAdelicGL_induction_over_places L n N hN p h1 (fun v x y hx hy => h2 v x hx y hy)

variable {L n}

theorem irr_of {a : NG.AlgWt L n} {S : Submodule ℂ (GAf L n → a.W)} (h : NG.IsIrrRep a.ρ S) :
    Irr (rtRep L n a.W) S :=
  ⟨h.1.stable, fun T hT hst => h.2.2 T ⟨hT.trans h.1.le, hst⟩ hT⟩

theorem orbit_fin {a : NG.AlgWt L n} {S₁ S₂ : Submodule ℂ (GAf L n → a.W)} (h₁ : NG.IsIrrRep a.ρ S₁)
    (h₂ : NG.IsIrrRep a.ρ S₂) {K : Subgroup (GAf L n)} (hK : K ≤ Umax L n) :
    ∀ x ∈ S₁ ⊔ S₂, ((fun k => rtRep L n a.W k x) '' (K : Set (GAf L n))).Finite := by
  intro x hx
  obtain ⟨N, hN, hx⟩ := (sup_le h₁.1.le h₂.1.le hx).2
  exact (GlobalTheory.IsotOrth.orbit_finite (rtRep L n a.W) hN x fun κ hκ => funext fun g => hx κ hκ g).subset
    (Set.image_mono hK)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert N hN hf
  refine GlobalTheory.T.exists_doubleCosetCommuting_map_principalCongruence L n a S₁ S₂ h₁ ?_ N hN hf
  obtain ⟨g₁, hg₁, hg₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨g₂, hg₂, hg₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂.2.1
  obtain ⟨M₁, hM₁, e₁⟩ := (h₁.1.le hg₁).2
  obtain ⟨M₂, hM₂, e₂⟩ := (h₂.1.le hg₂).2
  have hM : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have H := placeSys L n hM
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  obtain ⟨W, hW⟩ := graph_of_local H (irr_of h₁) (irr_of h₂) (orbit_fin h₁ h₂ fun k hk => hk.1)
    ((Submodule.ne_bot_iff _).2 ⟨g₁, ⟨hg₁, fun k hk => funext fun g => e₁ k (NG.Cong.of_mul_left L n hk) g⟩, hg₁0⟩)
    ((Submodule.ne_bot_iff _).2 ⟨g₂, ⟨hg₂, fun k hk => funext fun g => e₂ k (NG.Cong.of_mul_right L n hk) g⟩, hg₂0⟩)
    (by
      have := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hM
      refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ (M₁ * M₂)) ?_
      rintro f ⟨hfS, hfU⟩
      exact ⟨(h₁.1.le hfS).1, fun κ hκ g => congrFun (hfU κ hκ) g⟩)
    (fun v => by
      by_cases hv : ∃ s : SplitPlace L, s.v = v
      · obtain ⟨s, rfl⟩ := hv
        obtain ⟨σ₁, σ₂, l₁, l₂, he⟩ := hsplit s
        obtain ⟨X, x1, x2, x3, x4, x5⟩ := GlobalTheory.T.exists_stable_graph_of_iso_splitPlace_components L n a S₁ S₂ s σ₁ σ₂ l₁ l₂ he
        exact ⟨X, x1, x2, x3, x4, x5⟩
      · obtain ⟨w, Dv, α, -, ⟨f₁, hf₁, n₁, k₁⟩, ⟨f₂, hf₂, n₂, k₂⟩, hH⟩ := hinert v fun s hs => hv ⟨s, hs⟩
        refine graph_of_hecke (K := GlobalTheory.InertSph.Kv L n v) (H.comm v) (H.dec v) inf_le_right (irr_of h₁) (irr_of h₂)
          (orbit_fin h₁ h₂ inf_le_left) hf₁ hf₂ n₁ n₂ (fun k hk => k₁ k hk.1 hk.2) (fun k hk => k₂ k hk.1 hk.2)
          fun x hx => ?_
        obtain ⟨R, h, hR, hh, hA⟩ := GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
          (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
        have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
            (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
          fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
        have hKv : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ GlobalTheory.InertSph.Kv L n v ↔ κ ∈ Umax L n) :=
          fun κ hκ => ⟨fun h => h.1, fun h => ⟨h, hκ⟩⟩
        obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 x ⟨1, one_mem _, 1, one_mem _, by simp⟩
        refine ⟨R, Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α, ⟨γ, hγ⟩, hR.1, ?_, ?_⟩
        · refine (hA a.W f₁ k₁).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₁ k₁]
          exact (hH _ hKv h hh).1 f₁ hf₁ fun k hk => k₁ k hk.1 hk.2
        · refine (hA a.W f₂ k₂).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₂ k₂]
          exact (hH _ hKv h hh).2 f₂ hf₂ fun k hk => k₂ k hk.1 hk.2)
  exact GlobalTheory.T.equivariant_iso_of_translationStable_graph L n a.ρ a.ρ S₁ S₂ W h₁ h₂ hW.mem (fun h w hw => hW.stab h trivial w hw) hW.inj₁ hW.inj₂ hW.ne

end GlobalTheory.HeckeIso
