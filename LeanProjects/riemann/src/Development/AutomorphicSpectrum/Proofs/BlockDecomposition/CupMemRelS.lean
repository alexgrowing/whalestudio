import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AppendCons
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFinsetInf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Per
variable {K : Type} [Field K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}

theorem rs_topIso {V V' : Y.Opens} (h : V' ≤ V) (x : Γ(V, ⊤)) :
    rs h (V.topIso.hom.hom x) = V'.topIso.hom.hom ((Y.homOfLE h).appTop.hom x) := by
  rw [Scheme.homOfLE_appTop]
  simp only [rs, Scheme.Opens.topIso_hom, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def kerI (q : Y ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Y) (V : Y.Opens) : Ideal (Sec q V) := RingHom.ker (i.app V).hom

theorem one_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b j : ℕ)
    (hj : j ≠ b) : Subsingleton ((RC (G q b) P hQ).H j) := by
  subst hP
  exact (hAR K W Y q i hQ V d d' hc hc' b).1 j hj

theorem inj_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) :
    Function.Injective ((incl (G q b) P hQ).mapH b) := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).1

theorem range_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) (ω : Om K (Sec q V) b) :
    castH (G q b) hP b (E ω) ∈ LinearMap.range ((incl (G q b) P hQ).mapH b) ↔
      ω ∈ relOm K (kerI q i V) b := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).2 ω

theorem pull_P {V V' : Y.Opens} {P P' : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V) (hP' : P' = inU q V') (k : P' ≤ P)
    (b : ℕ) (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (E' : Om K (Sec q V') b →ₗ[K] HV q V' b b)
    (φ : Om K (Sec q V) b →ₗ[K] Om K (Sec q V') b)
    (h : ∀ (k' : inU q V' ≤ inU q V) ω, (resU (G q b) k').pull b (E ω) = E' (φ ω)) (ω : Om K (Sec q V) b) :
    (resU (G q b) k).pull b (castH (G q b) hP b (E ω)) = castH (G q b) hP' b (E' (φ ω)) := by
  subst hP hP'
  exact h k ω

theorem cup_P (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {V : Y.Opens} {P U₁ U₂ : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V)
    (k₁ : P ≤ U₁) (k₂ : P ≤ U₂) (β₁ : CH.Cn (U₁.ι ⋙ G q 1) 1) (β₂ : CH.Cn (U₂.ι ⋙ G q 1) 1) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V)
    (hf : ∀ (k₁' : inU q V ≤ U₁) (k₂' : inU q V ≤ U₂), ∃ hz, IsForm q V (a := 1) g₁ ![t]
      ((CH.cx ((inU q V).ι ⋙ G q 1)).cls ((resU (G q 1) k₁').pullC 1 β₁ - (resU (G q 1) k₂').pullC 1 β₂) hz))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn (P.ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = castH (G q a) hP a (E₂ ω))
    (hz : CH.d (P.ι ⋙ G q (a + 1)) (a + 1) ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) = 0) :
    (CH.cx (P.ι ⋙ G q (a + 1))).cls ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) hz =
      castH (G q (a + 1)) hP (a + 1) (E₃ (g₁ • w ω)) := by
  subst hP
  obtain ⟨hb, hform⟩ := hf k₁ k₂
  exact cup_form hFL hFU hFC E₂ E₃ h₂ h₃ g₁ t _ hb hform w hw y hy ω hcls hz

theorem cup_mem_relS {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {Q : ObjectProperty C} (hQ : Cosieve Q) {p n m : ℕ} (h : p + n = m) (b : CH.Cn F₁ p) (x : CH.Cn F₂ n) (hx : x ∈ relS F₂ Q n) :
    P.cupC h b x ∈ relS F₃ Q m := by
  intro s hs
  have hx' : x ((CH.back_mono h).functor ⋙ s) = 0 := hx _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs)
  change P.μ _ _ (CH.term F₂ s x (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx', map_zero, map_zero]

end Per

end GlobalTheory.CompanionTheory.RelKill
