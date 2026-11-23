import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwistInputsTest

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def zeroFam (i : X.Tw) : RFam Y i := ⟨fun _ _ => ⊥, fun _ _ => 0, fun _ _ => ⊥, fun _ _ => ∅⟩

def act (i : X.Tw) (j : ℕ) (b : Bool) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))

theorem act_single (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    act Y i j b (MonoidAlgebra.single g 1) x = Y.actG i j b g x := by
  simp [act]

theorem act_mem (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GStable Y i j b W) (z : MonoidAlgebra (FractionRing (X.O i)) (G0g N)) (x : Y.Fm i j b) (hx : x ∈ W) :
    act Y i j b z x ∈ W := by
  induction z using MonoidAlgebra.induction_on with
  | of g => simpa [act] using hW g x hx
  | add f g hf hg => rw [map_add]; exact W.add_mem hf hg
  | smul r f hf => rw [map_smul]; exact W.smul_mem r hf

theorem eG_on_irred (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GIrred Y i j b W) : (∀ x ∈ W, eG Y i j b x = x) ∨ (∀ x ∈ W, eG Y i j b x = 0) := by
  have he : eG Y i j b = act Y i j b (Y.eAlg i b) := rfl
  have hcomm : ∀ g x, eG Y i j b (Y.actG i j b g x) = Y.actG i j b g (eG Y i j b x) := by
    intro g x
    rw [he, ← act_single, ← act_single, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      Y.eAlg_central]
  have hid : ∀ x, eG Y i j b (eG Y i j b x) = eG Y i j b x := by
    intro x
    rw [he, ← Module.End.mul_apply, ← map_mul, Y.eAlg_idem]
  obtain ⟨-, hst, hmin⟩ := hW
  rcases hmin (W ⊓ LinearMap.ker (eG Y i j b)) inf_le_left (fun g x hx =>
    ⟨hst g x hx.1, by
      have h2 : eG Y i j b x = 0 := hx.2
      show eG Y i j b _ = 0
      rw [hcomm, h2, map_zero]⟩) with h | h
  · left
    intro x hx
    have : x - eG Y i j b x ∈ W ⊓ LinearMap.ker (eG Y i j b) :=
      ⟨W.sub_mem hx (act_mem Y i j b W hst _ x hx), by
        show eG Y i j b _ = 0
        rw [map_sub, hid, sub_self]⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this.symm
  · right
    intro x hx
    rw [← h] at hx
    exact hx.2

theorem act_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g x, Y.actG i j b g (T x) = T (Y.actG i j b g x))
    (z : MonoidAlgebra (FractionRing (X.O i)) (G0g N)) (x : Y.Fm i j b) :
    act Y i j b z (T x) = T (act Y i j b z x) := by
  induction z using MonoidAlgebra.induction_on with
  | of g => simpa [act] using hT g x
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem eG_actG (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    eG Y i j b (Y.actG i j b g x) = Y.actG i j b g (eG Y i j b x) := by
  have he : eG Y i j b = act Y i j b (Y.eAlg i b) := rfl
  rw [he, ← act_single, ← act_single, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    Y.eAlg_central]

theorem mem_typeSubspace_iff_unipotent_character (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : x ∈ Fm0 Y i j b ↔ ∀ u : Y.U,
    Y.actG i j b u x = ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  simp [Fm0, Submodule.mem_iInf, sub_eq_zero]

theorem goodPart_le_typeSubspace (i : X.Tw) (j : ℕ) (b : Bool) : V0 Y i j b ≤ Fm0 Y i j b := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_typeSubspace_iff_unipotent_character]
  intro u
  rw [← eG_actG, (mem_typeSubspace_iff_unipotent_character Y i j b x).1 hx u, map_smul]

theorem twOK_of_psiOk (i : X.Tw) (A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A Q k' ψ') (b : Bool) :
    TwOK i k' Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) ∧
      UnrG (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) ∧ Disjoint Q A := by
  classical
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ := h
  rw [Finset.disjoint_union_right] at h2
  set ψ := ψ'.comp (X.art i Q)
  have hu : UnrG ψ := by
    intro k v hv A' hA σ hσ
    by_contra hne
    have hQ : v ∈ (Q : Set (PlE D.host)) := (h7 v A' hA).1 ⟨σ, hσ, hne⟩
    exact Finset.disjoint_left.1 h2.1 hQ (X.placesOver_subset_exceptional i k hv)
  cases b
  · have hk : (ψ⁻¹).ker = ψ.ker := by ext g; simp [MonoidHom.mem_ker]
    refine ⟨⟨fun P hP => (h1 P hP).1, h2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_, h2.2⟩
    · show IsOpen (((ψ⁻¹).ker : Subgroup (G D.host.E N.Om)) : Set (G D.host.E N.Om)); rw [hk]; exact h4
    · intro g g' hg; show (ψ g')⁻¹ = ((ψ g)⁻¹)⁻¹; rw [h5 g g' hg]
    · intro g; exact Subgroup.inv_mem _ (h6 g)
    · intro v A' hA
      rw [← h7 v A' hA]
      exact exists_congr fun σ => and_congr_right fun _ => inv_ne_one
    · intro v hv A' hA σ hσ; exact inv_eq_one.2 (h8 v hv A' hA σ hσ)
    · intro k v hv A' hA σ hσ; exact inv_eq_one.2 (hu k v hv A' hA σ hσ)
  · exact ⟨⟨fun P hP => (h1 P hP).1, h2.1, h4, h5, h6, h7, h8⟩, hu, h2.2⟩

theorem admissibleGoodIdempotent_iff_reduced : GroupAlgebraIntegrality Y ↔ ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (b : Bool),
    (∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
        (Y.actG i j b g).toLinearMap ∘ₗ Y.hkF i j b k P = Y.hkF i j b k P ∘ₗ (Y.actG i j b g).toLinearMap :=
  ⟨fun h i hi b => ⟨(h i hi b).1, fun j hj => ((h i hi b).2 j hj).1⟩,
    fun h i hi b => ⟨(h i hi b).1, fun j hj => ⟨(h i hi b).2 j hj, fun _ W _ hW => eG_on_irred Y i j b W hW⟩⟩⟩

def admissibleIndexBoundAllPowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

end GlobalTheory.TwistInputsTest

end
