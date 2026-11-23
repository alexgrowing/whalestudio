import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7}

theorem prod_eq_inf (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) = P.inf fun w => w.asIdeal ^ d w :=
  (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun _ _ _ _ hne h => hne h).symm

theorem prod_ne_bot (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem idem_mem_OA {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : toEAf D e ∈ OA D := by
  obtain ⟨-, e1, e2⟩ := cpt_idemSum he
  refine (mem_OA_iff _).2 fun w => ?_
  by_cases hw : w ∈ P
  · rw [e1 w hw]; exact one_mem _
  · rw [e2 w hw]; exact zero_mem _

theorem one_sub_idem_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (d : Pl D.host.E → ℕ) :
    (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w) := by
  obtain ⟨-, e1, -⟩ := cpt_idemSum he
  refine mem_idS_of_v_le (w := fun w => w) (prod_ne_bot P d) (prod_eq_inf P d) fun w hw => ?_
  show Valued.v (cpt (D := D) w (1 - toEAf D e)) ≤ _
  rw [RingHom.map_sub, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
  exact zero_le'

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_map (hx : IsHalf e x) : x.map (toEAf D) = toEAf D e • x.map (toEAf D) :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← RingHom.map_mul, hx i j]

theorem fr_half (hx : IsHalf e x) (i : Fin T.V.rank) (j : Fin S.V.rank) :
    fr T.β S.β (x.map (toEAf D)) i j = toEAf D e * fr T.β S.β (x.map (toEAf D)) i j := by
  have h1 : fr T.β S.β (x.map (toEAf D)) i j = fr T.β S.β (toEAf D e • x.map (toEAf D)) i j := by
    rw [← half_map hx]
  rw [fr_smul, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

variable {S T : GlobalTheory.Grid.Node D}

theorem frMapO_eq_fr (x : WO S.V T.V) : frMapO S.V T.V S.β T.β x = fr T.β S.β (x.map (toEAf D)) := by
  unfold frMapO fr
  rfl

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

theorem alg_one {R : Type} [CommRing R] {s t A A' X Y E eS : R} (hs : s = E * (X - Y)) (ht : t = Y - A') (ha : A = A')
    (he : eS = E) (hx : X = E * X) : s + eS * t - (1 - eS) * A + A = X := by
  subst hs ht ha he
  linear_combination -hx

theorem alg_two {R : Type} [CommRing R] {s t A X eS : R} (h : s + eS * t - (1 - eS) * A + A = X) :
    X - A = s + eS * t - (1 - eS) * A := by
  rw [← h]; ring

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) := by
  rw [mul_sub, hx]; rfl

theorem fr_half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : fr T.β S.β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr T.β S.β (x.map (toEAf D)) i j - fr T.β S.β (y.map (eToEAf D)) i j) := by
  have h : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, half_sub hx, RingHom.map_mul, RingHom.map_sub]; rfl
  rw [h, fr_smul, fr_sub]; rfl

theorem sub_mem_hatMx {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ)
    (he : IsIdemSum e P) (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x)
    (h : ∀ i j, ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I) :
    x - e • (x₀.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ) := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  refine (mem_hatMx_iff hS hT _ _).2 ⟨fun i j => by rw [half_sub hx, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩
  obtain ⟨hX, h'⟩ := h i j
  refine ⟨⟨toEAf D e, idem_mem_OA he⟩ * (⟨_, hX⟩ - a i j), Ideal.mul_mem_left _ _ h', ?_⟩
  refine Eq.trans ?_ (fr_half_sub hx x₀.1 i j).symm
  exact congrArg (toEAf D e * ·) (congrArg₂ (· - ·) rfl (ha i j))

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

set_option maxHeartbeats 1000000 in

theorem frMapO_sub_mem {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ) (eS : OA D)
    (heS : eS.1 = toEAf D e) (he1 : 1 - eS ∈ idS D.host.F I)
    (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x) (y : homLat S.Λ T.Λ)
    (hyx : y.1 - x₀.1 ∈ I • homLat S.Λ T.Λ)
    (hz : x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ))
    (i : Fin T.V.rank) (j : Fin S.V.rank) : ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I := by
  obtain ⟨s, hs, hs'⟩ := ((mem_hatMx_iff hS hT _ _).1 hz).2 i j
  obtain ⟨t, ht, ht'⟩ := fr_mem_idS hS hT hyx i j
  have hs'' := hs'.trans (fr_half_sub hx y.1 i j)
  have hyA : t.1 = fr T.β S.β (y.1.map (eToEAf D)) i j - fr T.β S.β (x₀.1.map (eToEAf D)) i j := by
    rw [ht', Matrix.map_sub _ (RingHom.map_sub _), fr_sub, Matrix.sub_apply]
  have hz0 : s.1 + eS.1 * t.1 - (1 - eS.1) * (a i j).1 + (a i j).1 = fr T.β S.β (x.map (toEAf D)) i j :=
    alg_one hs'' hyA (ha i j) heS (fr_half hx i j)
  have hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have hz1 : ((s + eS * t - (1 - eS) * a i j + a i j : OA D) : EAf D) = fr T.β S.β (x.map (toEAf D)) i j := by
      simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
      exact hz0
    rw [frMapO_eq_fr, ← hz1]
    exact (s + eS * t - (1 - eS) * a i j + a i j).2
  refine ⟨hX, ?_⟩
  have : (⟨_, hX⟩ : OA D) - a i j = s + eS * t - (1 - eS) * a i j := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
    rw [frMapO_eq_fr]
    exact alg_two hz0
  rw [this]
  exact sub_mem (add_mem hs (Ideal.mul_mem_left _ _ ht)) (Ideal.mul_mem_right _ _ he1)

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D}

set_option maxHeartbeats 1000000 in

theorem cosetInd_eq_of {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ)
    (hT : IsFrame T.β T.Λ) (he : IsIdemSum e P) (he1 : (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F I)
    (κ : Cos S.Λ T.Λ I) (x₀ : homLat S.Λ T.Λ) (hx₀ : Cos.mk I x₀ = κ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (c : Coset S T I)
    (hc : ∀ i j, cmpS D.host.F I (c i j) = Ideal.Quotient.mk (idS D.host.F I) (a i j)) :
    cosetInd S T e I c = cosInd e κ := by
  funext x
  have key : IsHalf e x → (InCosetOf S T I c x ↔ ∃ y : homLat S.Λ T.Λ, Cos.mk I y = κ ∧
      x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ)) := by
    intro hx
    have hq : ∀ i j (hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        Ideal.Quotient.mk (idS D.host.F I) ⟨_, hX⟩ = cmpS D.host.F I (c i j) ↔ (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I :=
      fun i j hX => by rw [hc i j, Ideal.Quotient.eq]
    constructor
    · intro h
      exact ⟨x₀, hx₀, sub_mem_hatMx hS hT he x₀ a ha hx fun i j => ⟨(h i j).1, (hq i j _).1 (h i j).2⟩⟩
    · rintro ⟨y, hy, hz⟩ i j
      obtain ⟨hX, h'⟩ := frMapO_sub_mem hS hT _ rfl he1 x₀ a ha hx y (sub_mem_of_mk_eq (hy.trans hx₀.symm)) hz i j
      exact ⟨hX, (hq i j hX).2 h'⟩
  have hiff : (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ cosSet e κ :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  by_cases h : x ∈ cosSet e κ
  · rw [if_pos (hiff.2 h), Set.indicator_of_mem h]; rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem cosInd_eq_cosetInd : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he κ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : homLat S.Λ T.Λ, Cos.mk (∏ w ∈ P, w.asIdeal ^ d w) x₀ = κ :=
    Submodule.Quotient.mk_surjective _ κ
  have hA : ∀ i j, ∃ s : OA D, s.1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j := fun i j => by
    obtain ⟨s, -, hs⟩ := fr_mem_idS hS hT (𝔪 := ⊤) (y := x₀.1) (by rw [Submodule.top_smul]; exact x₀.2) i j
    exact ⟨s, hs⟩
  choose a ha using hA
  choose c hc using fun i j => cmpS_surj (F := D.host.F) _ (prod_ne_bot P d)
    (Ideal.Quotient.mk (idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w)) (a i j))
  exact ⟨fun i j => c i j, cosetInd_eq_of hS hT he (one_sub_idem_mem he d) κ x₀ hx₀ a ha _ fun i j => hc i j⟩

end GlobalTheory.CosToCoset
