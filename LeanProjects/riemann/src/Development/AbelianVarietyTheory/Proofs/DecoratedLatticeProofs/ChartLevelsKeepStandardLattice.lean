import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KLat

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev IA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem inclE_mem_IA (r : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (r : E) ∈ IA F E :=
  Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)

theorem sigR_mem_IA (σ : E →ₐ[F] E) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hy : y ∈ IA F E) :
    Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ IA F E := by
  have h : IA F E ≤ (IA F E).comap (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, ⟨r, rfl⟩⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
    · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 E) E r)) :=
        (NumberField.RingOfIntegers.isIntegral_coe r).map (RingHom.toIntAlgHom (σ : E →+* E))
      have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) =
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((⟨_, hi⟩ : 𝓞 E) : E)) := rfl
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact inclE_mem_IA (F := F) (⟨_, hi⟩ : 𝓞 E)
    · have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F) := by
        simp [Formalism.UG.sigR]
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  exact h hy

variable {n : ℕ}

def HatP (π : 𝓞 E) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ j : Fin n, x j ∈ IA F E ∧
    (j.1 + 1 = n → ∃ s ∈ IA F E, x j = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((π : 𝓞 E) : E) * s)

theorem hatP_of_mem (π : 𝓞 E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L → ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    {x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (IA F E) L) : HatP π x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    intro j
    obtain ⟨r, hr, hd⟩ := hL z hz j
    refine ⟨by simp only [hr]; exact inclE_mem_IA r, fun hj => ?_⟩
    obtain ⟨t, rfl⟩ := hd hj
    refine ⟨_, inclE_mem_IA t, ?_⟩
    show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j) = _
    rw [hr, ← map_mul]; rfl
  | zero => intro j; exact ⟨zero_mem _, fun _ => ⟨0, zero_mem _, by simp⟩⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    obtain ⟨b1, b2⟩ := hy j
    refine ⟨add_mem a1 b1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    obtain ⟨s', hs', e'⟩ := b2 hj
    exact ⟨s + s', add_mem hs hs', by simp only [Pi.add_apply, e, e', mul_add]⟩
  | smul c x _ hx =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    have ec : (c • x) j = (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j := rfl
    refine ⟨by rw [ec]; exact mul_mem c.2 a1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    exact ⟨(c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s, mul_mem c.2 hs, by rw [ec, e]; ring⟩

end Gen

end GlobalTheory.KLat

namespace GlobalTheory.KLat

section Lev
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem inv_eq_cT {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (lev : StepLevel F E σ J T f bad)
    {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 a b = Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (g.1 b a) := by
  have hu := ((lev.U_eq g).1 hg).1
  have h : Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * g.1 =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
  rw [hJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have e : (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 = Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 := by
    calc (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1
        = (Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * g.1) * (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 := by
          rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e]
  rfl

variable (π : 𝓞 E) {J : Matrix (Fin n) (Fin n) E} (lev : StepLevel F E σ J T f bad)
  (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))

include hLb in
theorem img_hatP {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (y : Fin n → E) (hy : y ∈ lev.Lb) :
    HatP π (g.1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) :=
  hatP_of_mem π lev.Lb (fun x hx => (hLb x).1 hx)
    ((GlobalTheory.Mem.Col2.SameOff.stepLevel_stab lev g hg _).1 (Submodule.subset_span ⟨y, hy, rfl⟩))

theorem incl_single (j : Fin n) (c : E) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j c : Fin n → E) i)) =
      Pi.single j (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) c) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]

include hLb in

theorem col_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (j : Fin n) (hj : ¬ j.1 + 1 = n)
    (a : Fin n) : g.1 a j ∈ IA F E := by
  have hy : (Pi.single j 1 : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp, fun h => absurd h hj⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  have h := (img_hatP π lev hLb hg _ hy a).1
  rw [incl_single, map_one, Matrix.mulVec_single_one] at h
  simpa using h

include hLb in
theorem pi_ne_zero (l : Fin n) (hl : l.1 + 1 = n) : π ≠ 0 := by
  intro h0
  have hsub : (lev.Lb : Set (Fin n → E)) ⊆ (LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) : Set (Fin n → E)) := by
    intro x hx
    obtain ⟨r, hr, hd⟩ := (hLb x).1 hx l
    have hr0 : r = 0 := by rw [h0] at hd; exact zero_dvd_iff.1 (hd hl)
    simp [LinearMap.mem_ker, hr, hr0]
  have h2 := Submodule.span_le.2 hsub
  rw [lev.Lb_span, top_le_iff] at h2
  have h1 : (Pi.single l 1 : Fin n → E) ∈ LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) := by
    rw [h2]; trivial
  simp at h1

include hLb in

theorem last_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (l : Fin n) (hl : l.1 + 1 = n) :
    g.1 l l ∈ IA F E := by
  have hy : (Pi.single l (π : E) : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = l
    · subst hk; exact ⟨π, by simp, fun _ => dvd_rfl⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  obtain ⟨s, hs, e⟩ := (img_hatP π lev hLb hg _ hy l).2 hl
  rw [incl_single, Matrix.mulVec_single] at e
  have hπ : (π : E) ≠ 0 := fun h => pi_ne_zero π lev hLb l hl (by exact_mod_cast h)
  have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E)) := (IsUnit.mk0 _ hπ).map _
  have e2 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * g.1 l l = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * s := by
    rw [mul_comm]; exact e
  rw [hu.mul_left_cancel e2]
  exact hs

include hLb in

theorem entry_mem (hJ : J = 1) {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ IA F E := by
  by_cases hb : b.1 + 1 = n
  · by_cases ha : a.1 + 1 = n
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      exact last_mem π lev hLb hg a ha
    · have hi : g⁻¹ ∈ lev.U := inv_mem hg
      have e := inv_eq_cT hJ lev hi a b
      rw [inv_inv] at e
      rw [e]
      exact sigR_mem_IA σ (col_mem π lev hLb hi a ha b)
  · exact col_mem π lev hLb hg b hb a

theorem entry_memD {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (π : 𝓞 D.host.E) (lev : StepLevel D.host.F D.host.E (sigD D) J T f bad)
    (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → π ∣ r))
    (hJ : J = 1) {g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  entry_mem π lev hLb hJ hg a b

end Lev

end GlobalTheory.KLat

namespace GlobalTheory.AdForm

theorem levels_keep_stdLat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  intro B X I hI _ l Z u a Ch A hA i hi β k hk
  obtain ⟨-, κ, hκ⟩ := (hA.U i hi β k).1 hk
  have hV : ((I.rec7 l Z).sp.X i).gram = 1 := hI.gram_X i
  refine GlobalTheory.SplitDec.moves_std hV _ ?_
  have hJ : gramN (I.rec7 l Z) i hi = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hLb := (hA.reads i hi).lb β
  intro p q
  have e : toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ k p q) =
      finM _ (rankN (I.rec7 l Z) i hi) k (finCongr (rankN _ i hi) p) (finCongr (rankN _ i hi) q) := by
    simp [finM, Matrix.reindex_apply]
  rw [e, ← hκ]
  have hLb' : ∀ x, x ∈ (A.K i hi β).lev.Lb ↔ ∀ j : Fin ((I.rec7 l Z).R.N i), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.N i → (X.piT u : 𝓞 (I.rec7 l Z).host.E) ∣ r) :=
    fun x => hLb x
  exact GlobalTheory.KLat.entry_memD _ (A.K i hi β).lev hLb' hJ κ.2 _ _

end GlobalTheory.AdForm
