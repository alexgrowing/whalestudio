import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar

theorem addValuation_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 < Examples₂.PlacesToy.valW w x ↔ w.valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [Examples₂.PlacesToy.valW_of_ne w hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem addValuation_pos_iff_mem_asIdeal {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    0 < Examples₂.PlacesToy.valW w (x : K) ↔ x ∈ w.asIdeal := by
  rw [addValuation_pos_iff_valuation_lt_one, ← w.valuation_lt_one_iff_mem (K := K)]

theorem addVal_pos_iff {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) :
    0 < v x ↔ ¬ 0 ≤ v x⁻¹ := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  generalize v x = a at h
  generalize v x⁻¹ = b at h
  cases a with
  | top => simp at h
  | coe a =>
    cases b with
    | top => simp at h
    | coe b =>
      norm_cast at h ⊢
      omega

theorem overOne_plUnder (X : Stages) {B' : Base} (h : Enl X.B B') (v v' : B'.places.Pl)
    (hv : ∀ x ∈ B'.LL0, 0 ≤ B'.places.val v x ↔ 0 ≤ B'.places.val v' x) :
    OverOne X.toD7 (plUnder h v) (plUnder h v') := by
  intro x
  let y : 𝓞 X.B.LL := algebraMap (𝓞 ↥X.B.LL0) (𝓞 X.B.LL) x
  have key : ∀ u : B'.places.Pl, 0 < Examples₂.PlacesToy.valW (K := X.B.LL) (plUnder h u) (y : X.B.LL) ↔
      0 < Examples₂.PlacesToy.valW (K := B'.LL) u (incl h (y : X.B.LL)) := fun u =>
    (addValuation_pos_iff_mem_asIdeal _ y).trans ((mem_plUnder h u y).trans
      (addValuation_pos_iff_mem_asIdeal (K := B'.LL) u (RingOfIntegers.mapRingHom (incl h) y)).symm)
  have hm : incl h (y : X.B.LL) ∈ B'.LL0 := by
    have h1 : X.B.embLL (y : X.B.LL) ∈ B'.embLL '' ↑B'.LL0 := h.2.2.1 ▸ ⟨_, (x : ↥X.toD7.LL0).2, rfl⟩
    obtain ⟨z, hz, e⟩ := h1
    rw [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
    exact hz
  refine (key v).trans (Iff.trans ?_ (key v').symm)
  by_cases h0 : incl h (y : X.B.LL) = 0
  · rw [h0, AddValuation.map_zero, AddValuation.map_zero]
  · rw [addVal_pos_iff _ h0, addVal_pos_iff _ h0]
    exact not_congr (hv _ (B'.LL0.inv_mem hm))

theorem Seed.psiOk {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) {v : D.what₂.places.Pl} (hv : TwistedAt D v) :
    BlochKatoReduction.Gen.PsiOk (σ.s v) (A (σ.s v)) (σ.Q (σ.s v)) (σ.k (σ.s v)) (σ.ψ (σ.s v)) := by
  classical
  have h := ((σ.good v hv).2 1 (by simp)).1
  rw [zpow_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

theorem exists_coh_twFrom : PrN → ∀ (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (σ : Seed X.toD7 A) (Av : ℕ → Finset ℕ), (∀ v, TwistedAt X.toD7 v → X.B.places.resChar v ∈ pl) → (∀ v v', OverOne X.toD7 v v' → TwistedAt X.toD7 v → TwistedAt X.toD7 v') → (∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i)) → ∀ S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ, (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) → ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (h : Enl X.B B'), HEq f' f ∧ T'.pl = pl ∧ T'.Avoids Av ∧ (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ Coh B' T' ∧ TwFrom X σ h T' := by
  intro hP X f pl A σ Av hpl hsat hA S₂ h₂
  obtain ⟨art, ha⟩ := hP.what₂.art X.toD7.host.E X.toD7.nd.Om
  obtain ⟨h1, T₁, e1, hav, hT, hT', hS⟩ := exists_twDat_stagesOn X f pl {v | TwistedAt X.toD7 v} hpl
    (twistedAt_conj X.toD7) σ.s (fun w => let ⟨_, hb⟩ := σ.reads w; hb.l_eq) (fun w _ => σ.conj w) art ha A σ.Q σ.k σ.ψ
    (fun i => rootIsoAt X.toD7 i (σ.k i)) Av hA (fun w hw => σ.psiOk hw)
  obtain ⟨B', h, a, b, e⟩ := hS (S₂ X.B.toPre f (T₁.set f)) (h₂ _ _ _)
  have e2 : ∀ (P : Pre) (_ : P = X.B.toPre) (g : Fr P) (Ξ : Set (HChar P.host.E)), HEq g f → HEq Ξ (T₁.set f) →
      S₂ P g Ξ = S₂ X.B.toPre f (T₁.set f) := by
    intro P eP g Ξ h1 h2
    subst eP
    rw [eq_of_heq h1, eq_of_heq h2]
  refine ⟨B', tr h.1 Fr f, pull h T₁, h, tr_heq _ _ _, e1, avoids_pull h hav, ?_, ⟨fun v v' hv => ?_, fun v => ?_⟩,
    b, fun v => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [e2 _ h.1 _ _ (tr_heq _ _ _) e]
    exact a
  · have ho := overOne_plUnder X h v v' hv
    have key : T₁.psi (plUnder h v) = T₁.psi (plUnder h v') ∧ T₁.Q (plUnder h v) = T₁.Q (plUnder h v') ∧
        T₁.k (plUnder h v) = T₁.k (plUnder h v') := by
      by_cases hw : TwistedAt X.toD7 (plUnder h v)
      · have hw' := hsat _ _ ho hw
        obtain ⟨x, y, z⟩ := hT _ hw
        obtain ⟨x', y', z'⟩ := hT _ hw'
        rw [σ.same _ _ hw hw' ho] at x' y' z'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
      · have hw' : ¬ TwistedAt X.toD7 (plUnder h v') := fun h' => hw (hsat _ _ (fun x => (ho x).symm) h')
        obtain ⟨x, y, z⟩ := hT' _ hw
        obtain ⟨x', y', z'⟩ := hT' _ hw'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
    exact ⟨congrArg (tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E)))) key.2.1, key.2.2,
      congrArg (tr h.1 (fun P => HChar P.host.E)) key.1⟩
  · have hn : B'.places.resChar v ^ (pull h T₁).k v ≠ 0 := pow_ne_zero _ (B'.places.resChar_prime v).ne_zero
    have hz := Complex.isPrimitiveRoot_exp _ hn
    obtain ⟨x, hx⟩ := b v _ hz.pow_eq_one
    exact ⟨x, IsPrimitiveRoot.of_map_of_injective (hx ▸ hz) B'.embLL.injective⟩
  · obtain ⟨x, y, z⟩ := hT (plUnder h v) hw
    exact ⟨(tr_heq h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) _).trans (heq_of_eq y), z, _, _,
      (h1 _ (σ.psiOk hw)).2.1, (tr_heq h.1 (fun P => HChar P.host.E) _).trans (heq_of_eq x)⟩
  · exact (congrArg (tr h.1 (fun P => HChar P.host.E)) (hT' _ hw).1).trans (tr_one _)

end GlobalTheory.HeightCounting.Up

end
