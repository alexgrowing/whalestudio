import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverRelationUniqueness
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocGenMass

open GlobalTheory.HL.PairingClass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {V : Type} [AddCommGroup V] [Module E V]

theorem frames_in_class (M : Model F E) (hM : M.OK) (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r)
    (hrk : Module.finrank E V = k + 2 * r + 1) (hP : P.RelG (LocNG.theta M))
    (d₁ : LocNG.Datum P) (t₁ : Term V M r) (ht₁ : LocNG.IsTermOver P d₁ t₁)
    (f f' : Fin (r + 1) → V) (hf : ∃ n ∈ P.A.N, f = fun b => n (P.A.f b))
    (hf' : ∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b))
    (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (hc1 : c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'}) (hZ1 : H.Zhat t₁.f t₁.f' ∈ c1) (hZ : H.Zhat f f' ∈ c1) :
    ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      Tied M.L.O (algebraMap F E (LocNG.theta M)) A A' ∧
      f = act (fun i => s (t₁.f i)) A ∧ f' = act (fun i => s (t₁.f' i)) A' := by
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨-, hN, hN', hSt, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨on, on', -⟩ := FrameOnto.unipotent_onto M.L r k S
  obtain ⟨-, stab⟩ := FrameStab.stab_eq M.L r k S
  have hmem : ∀ Y, Y ∈ c1 ↔ ∃ A A', Tied M.L.O (algebraMap F E (LocNG.theta M)) A A' ∧
      Y = cT M.L A * Y0 * A' := by
    intro Y
    rw [hc1]
    constructor
    · rintro ⟨A, A', h1, h2, h3, h4⟩
      exact ⟨A, A', (tied_iff_span _ _ _ _).1 ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨A, A', h, h4⟩
      obtain ⟨h1, h2, h3⟩ := (tied_iff_span _ _ _ _).2 h
      exact ⟨A, A', h1, h2, h3, h4⟩
  have hfr : ∀ g g' : Fin (r + 1) → V, (∃ n ∈ P.A.N, g = fun b => n (P.A.f b)) →
      (∃ n' ∈ P.B.N, g' = fun b => n' (P.B.f b)) →
      ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, UT u ∧ UT u' ∧ g = act P.A.f u ∧ g' = act P.B.f u' := by
    rintro g g' ⟨n, hn, e⟩ ⟨n', hn', e'⟩
    obtain ⟨u, hu, h⟩ := on _ ((hN n).1 hn)
    obtain ⟨u', hu', h'⟩ := on' _ ((hN' n').1 hn')
    exact ⟨u, u', hu, hu', e.trans (pull c n _ _ c.f_eq u h), e'.trans (pull c n' _ _ c.f'_eq u' h')⟩
  have hZ0 : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    simp only [Frames.Zh, HermSp.Zhat, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  obtain ⟨a₁, a₁', ha₁, e₁⟩ := (hmem _).1 hZ1
  obtain ⟨a, a', ha, e⟩ := (hmem _).1 hZ
  obtain ⟨b₁, b₁', hb₁, p1, -, p1', -⟩ := ha₁.inv
  have hA := hb₁.mul ha
  have eZ : H.Zhat f f' = cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') := by
    have : cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') =
        cT M.L (a₁ * b₁ * a) * Y0 * (a₁' * b₁' * a') := by
      simp only [e₁, cT_mul, mul_assoc]
    rw [this, p1, p1', one_mul, one_mul, e]
  generalize b₁ * a = A at hA eZ
  generalize b₁' * a' = A' at hA eZ
  obtain ⟨B, B', hB, q1, q2, q1', q2'⟩ := hA.inv
  obtain ⟨-, -, ⟨n₁, hn₁, e₁f, -⟩, ⟨n₁', hn₁', e₁f', -⟩, -⟩ := ht₁
  obtain ⟨u₁, u₁', hu₁, hu₁', f₁, f₁'⟩ := hfr _ _ ⟨n₁, hn₁, e₁f⟩ ⟨n₁', hn₁', e₁f'⟩
  obtain ⟨u, u', hu, hu', f₀, f₀'⟩ := hfr _ _ hf hf'
  obtain ⟨v, hv, w1, w2, -⟩ := hu₁.inv
  obtain ⟨v', hv', w1', w2', -⟩ := hu₁'.inv
  rw [f₀, f₀', f₁, f₁', Zhat_act, Zhat_act, ← hZ0] at eZ
  have key : cT M.L (u * B * v) * S.Zh * (u' * B' * v') = S.Zh := by
    have h1 : cT M.L (u * B * v) * S.Zh * (u' * B' * v') =
        cT M.L (B * v) * (cT M.L u * S.Zh * u') * (B' * v') := by
      simp only [cT_mul, mul_assoc]
    have h2 : cT M.L (B * v) * (cT M.L A * (cT M.L u₁ * S.Zh * u₁') * A') * (B' * v') =
        cT M.L (u₁ * (A * B) * v) * S.Zh * (u₁' * (A' * B') * v') := by
      simp only [cT_mul, mul_assoc]
    rw [h1, eZ, h2, q1, q1', mul_one, mul_one, w1, w1', cT_one, one_mul, mul_one]
  obtain ⟨h, hh, g1, g2⟩ := (stab _ _ ((hu.mul hB.1).mul hv) ((hu'.mul hB.2.1).mul hv')).1 key
  obtain ⟨s, rfl⟩ := c.grp.surjective h
  have k1 := pull c s _ _ c.f_eq _ g1
  have k2 := pull c s _ _ c.f'_eq _ g2
  refine ⟨s, (hSt s).2 hh, A, A', hA, ?_, ?_⟩
  · rw [f₀, f₁, map_act, k1, act_act, act_act]
    congr 1
    have : u * B * v * (u₁ * A) = u * (B * (v * u₁) * A) := by simp only [mul_assoc]
    rw [this, w2, mul_one, q2, mul_one]
  · rw [f₀', f₁', map_act, k2, act_act, act_act]
    congr 1
    have : u' * B' * v' * (u₁' * A') = u' * (B' * (v' * u₁') * A') := by simp only [mul_assoc]
    rw [this, w2', mul_one, q2', mul_one]

end GlobalTheory.HL.LocGenMass

namespace GlobalTheory.HL.LocGenMass

open GlobalTheory.HL.PairingClass

theorem act_one' {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (g : Fin n → V) : act g (1 : Matrix (Fin n) (Fin n) E) = g := by
  funext j
  simp [act, Matrix.one_apply]

theorem span_act_eq {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (O : Subring E) (g₀ : Fin n → V) (C : Matrix (Fin n) (Fin n) E) (hU : UT C) (hC : IntM O C) :
    Submodule.span O (Set.range (act g₀ C)) = Submodule.span O (Set.range g₀) := by
  have key : ∀ (g : Fin n → V) (D : Matrix (Fin n) (Fin n) E), IntM O D →
      Submodule.span O (Set.range (act g D)) ≤ Submodule.span O (Set.range g) := by
    intro g D hD
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (⟨D i j, hD i j⟩ : O) (Submodule.subset_span ⟨i, rfl⟩)
  refine le_antisymm (key _ _ hC) ?_
  obtain ⟨B, -, hCB, -, hint⟩ := hU.inv
  have e : act (act g₀ C) B = g₀ := by rw [act_act, hCB, act_one']
  have := key (act g₀ C) B (hint O hC)
  rwa [e] at this

theorem relift {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (δ : S.Datum) (Λ : Submodule L.O S.V) (m₀ m₀' m m' : S.GLV)
    (hW : S.IsTermW δ Λ m₀ m₀') (hm : m ∈ S.N) (hm' : m' ∈ S.N')
    (hc : ((fun b => m (S.f b)), (fun b => m' (S.f' b))) ∈
      S.frameCls (fun b => m₀ (S.f b)) (fun b => m₀' (S.f' b))) :
    ∃ m₂ ∈ S.N, ∃ m₂' ∈ S.N', (∀ b, m₂ (S.f b) = m (S.f b)) ∧ (∀ b, m₂' (S.f' b) = m' (S.f' b)) ∧
      S.IsTermW δ Λ m₂ m₂' := by
  obtain ⟨hA, hA', hn₀, hn₀', e, e', hth, hgr⟩ := hW
  obtain ⟨C, C', a3, a4, a12, adiag, aθ, p1, p2⟩ := hc
  have p1 : ∀ j, m (S.f j) = ∑ i, C i j • m₀ (S.f i) := p1
  have p2 : ∀ j, m' (S.f' j) = ∑ i, C' i j • m₀' (S.f' i) := p2
  have pf : (fun b => m (S.f b)) = act (fun b => m₀ (S.f b)) C := funext p1
  have pf' : (fun b => m' (S.f' b)) = act (fun b => m₀' (S.f' b)) C' := funext p2
  have hU : UT C := ⟨fun i j h => (a12 i j h).1, fun i => (adiag i).1⟩
  have hU' : UT C' := ⟨fun i j h => (a12 i j h).2, fun i => (adiag i).2⟩
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  obtain ⟨s1, s2, s3⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨s1', s2', s3'⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := TermBasic.isSD_smul S hn₀.1.1 s1
    rwa [← e] at this
  have tr : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m₀ (S.f b)) := by
    intro x
    have := TermBasic.trace_smul hg hn₀ (s2 (r + 1) le_rfl) x
    rwa [← e, hs, Set.image_univ] at this
  have tr' : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m₀' (S.f' b)) := by
    intro x
    have := TermBasic.trace_smul hg' hn₀' (s2' (r + 1) le_rfl) x
    rwa [← e', hs, Set.image_univ] at this
  have prim : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m (S.f b)) := by
    intro x
    rw [tr, pf, span_act_eq L.O _ C hU a3]
  have prim' : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m' (S.f' b)) := by
    intro x
    rw [tr', pf', span_act_eq L.O _ C' hU' a4]
  obtain ⟨A₁, hA₁, n₁, hn₁, hfix, hΛ₁⟩ :=
    GlobalTheory.HL.FrameLift.lift L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) Λ hSD m hm prim
  obtain ⟨A₁', hA₁', n₁', hn₁', hfix', hΛ₁'⟩ :=
    GlobalTheory.HL.FrameLift.lift L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) Λ hSD m' hm' prim'
  have eA : A₁ = δ.1 := by
    ext x
    rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA₁).2.2 x, s3 x,
      TermBasic.inner_smul S hn₁ (Λ := S.stdLat S.f S.es A₁),
      TermBasic.inner_smul S hn₀ (Λ := S.stdLat S.f S.es δ.1), ← hΛ₁, ← e]
  have eA' : A₁' = δ.2.1 := by
    ext x
    rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA₁').2.2 x, s3' x,
      TermBasic.inner_smul S hn₁' (Λ := S.stdLat S.f' S.es' A₁'),
      TermBasic.inner_smul S hn₀' (Λ := S.stdLat S.f' S.es' δ.2.1), ← hΛ₁', ← e']
  subst eA eA'
  refine ⟨n₁, hn₁, n₁', hn₁', hfix, hfix', hA, hA', hn₁, hn₁', hΛ₁, hΛ₁', fun j => ?_, hgr⟩
  rw [hfix, hfix', p1, p2]
  choose y hy hyeq using hth
  choose cc hcc hcceq using aθ
  have hmem : ∀ i, m₀ (S.f i) ∈ Λ := fun i => ((tr _).2 (Submodule.subset_span ⟨i, rfl⟩)).1
  refine ⟨∑ i, ((⟨C' i j, a4 i j⟩ : L.O) • y i + (⟨cc i j, hcc i j⟩ : L.O) • m₀ (S.f i)),
    Submodule.sum_mem _ fun i _ => Submodule.add_mem _ (Submodule.smul_mem _ _ (hy i))
      (Submodule.smul_mem _ _ (hmem i)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : m₀' (S.f' i) = m₀ (S.f i) + algebraMap F E S.th • y i := by
    rw [← hyeq i, add_sub_cancel]
  have h2 : C' i j = C i j + algebraMap F E S.th * cc i j := by
    rw [← hcceq i j, add_sub_cancel]
  rw [h1, Subring.smul_def, Subring.smul_def]
  simp only [h2]
  module

end GlobalTheory.HL.LocGenMass

namespace GlobalTheory.HL.LocGenMass

theorem mass_class_eq_weight_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrank hrel R d0 f f' hf hf' Y0 c1 hc1 hZ hex
  letI := hM.loc
  letI := hM.char0
  obtain ⟨d₁, t₁, ht₁, hZ₁⟩ := hex
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrank hrel
  obtain ⟨hT1, hT2, -⟩ := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨hth, hN, hN', hSt, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, hbij, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  have aS := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S
  have cls := GlobalTheory.HL.FrameClass.frame_classes M.L r k S
  have trm := GlobalTheory.HL.TermBasic.term_basic M.L r k S
  have vol := (GlobalTheory.HL.volSt M.L r k S).2
  obtain ⟨s₀, hs₀, A, A', hAA, ef, ef'⟩ :=
    frames_in_class M hM H r k P hrank hrel d₁ t₁ ht₁ f f' hf hf' Y0 c1 hc1 hZ₁ hZ
  obtain ⟨n, hn, rfl⟩ := hf
  obtain ⟨n', hn', rfl⟩ := hf'
  have h₁ := (hT1 d₁ t₁ ht₁).1
  have hs₀' : c.grp s₀ ∈ S.St := (hSt s₀).1 hs₀
  have hΛ₁t : S.IsTerm (c.dat d₁) (c.grp s₀ • c.lat t₁.abelian₂) := (aS _ _ h₁ _ hs₀').1
  set C₂ := S.Fr (c.dat d₁) (c.grp s₀ • c.lat t₁.abelian₂) with hC₂
  have hC₂' : C₂ = S.frameCls (fun b => c.e (n (P.A.f b))) (fun b => c.e (n' (P.B.f b))) := by
    rw [hC₂, (aS _ _ h₁ _ hs₀').2.2.2.2.1, GlobalTheory.HL.AbsGenMass.fr_eq hM c d₁ t₁ ht₁, (cls _ _).2.2]
    obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hAA
    refine ((cls (fun b => c.grp s₀ (c.e (t₁.f b))) (fun b => c.grp s₀ (c.e (t₁.f' b)))).2.1
      (fun b => c.e (n (P.A.f b)), fun b => c.e (n' (P.B.f b))) ⟨A, A', a3, a4, fun i j h => ⟨a1.1 i j h, a2.1 i j h⟩,
      fun i => ⟨a1.2 i, a2.2 i⟩, fun i j => ⟨C i j, hC i j, ?_⟩, fun j => ?_, fun j => ?_⟩).1.symm
    · rw [e1, ← hth]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · have := congrFun ef j
      simp only [PairingClass.act] at this
      simp [this, CoordUnip.grp_apply]
    · have := congrFun ef' j
      simp only [PairingClass.act] at this
      simp [this, CoordUnip.grp_apply]
  have hI : S.IsIntCls C₂ := (trm _ _ hΛ₁t).2.2.2.2.2.2.1
  obtain ⟨-, -, hw1, hwinv⟩ := vol C₂ hI.1
  refine ⟨S.wC C₂, by linarith, ?_, ?_⟩
  · have hsum := GlobalTheory.HL.TotalWeight.sumCls_one_le M.L r k S ⟨_, _, hΛ₁t⟩
    have hle : ENNReal.ofReal (S.wC C₂) ≤ S.sumCls fun _ => 1 := by
      unfold Frames.sumCls
      refine le_trans ?_ (ENNReal.le_tsum (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂))
      have hrl : (MulAction.orbitRel S.St (Set S.FrP))
          (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂).out C₂ := Quotient.mk_out C₂
      obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrl
      have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂).out = h • C₂ := e.symm
      have hint : S.IsIntCls (h • C₂) := by
        rw [hC₂, ← (aS _ _ hΛ₁t h hh).2.2.2.2.1]
        exact (trm _ _ (aS _ _ hΛ₁t h hh).1).2.2.2.2.2.2.1
      rw [e', if_pos hint, hwinv h hh, mul_one]
    rw [(GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c).1]
    have := hle.trans hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by unfold Frames.Hp; positivity)).1 this
  · have conv : ∀ (s : Set (Term V M r)) (p : Term V M r → Prop) [∀ t, Decidable (p t)] (g : Term V M r → ℝ≥0∞),
        (∑' t : s, if p t.1 then g t.1 else 0) = ∑' t : {t // t ∈ s ∧ p t}, g t.1 := by
      intro s p _ g
      rw [tsum_subtype s (fun t => if p t then g t else 0)]
      rw [show (∑' t : {t // t ∈ s ∧ p t}, g t.1) = ∑' t : ({t | t ∈ s ∧ p t} : Set _), g t.1 from rfl,
        tsum_subtype]
      refine tsum_congr fun t => ?_
      by_cases h1 : t ∈ s <;> by_cases h2 : p t <;> simp [Set.indicator, h1, h2]
    have orb : ∀ X : Set S.FrP, (∃ s ∈ S.St, X = s • S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) ↔
        ∃ s ∈ S.St, X = s • C₂ := by
      intro X
      rw [hC₂, (aS _ _ h₁ _ hs₀').2.2.2.2.1]
      constructor
      · rintro ⟨s, hs, e⟩
        refine ⟨s * (c.grp s₀)⁻¹, S.St.mul_mem hs (S.St.inv_mem hs₀'), ?_⟩
        rw [e, mul_smul, inv_smul_smul]
      · rintro ⟨s, hs, e⟩
        refine ⟨s * c.grp s₀, S.St.mul_mem hs hs₀', ?_⟩
        rw [e, mul_smul]
    have hC₁ := GlobalTheory.HL.AbsGenMass.fr_eq hM c d₁ t₁ ht₁
    have hclass : ∀ d t, LocNG.IsTermOver P d t →
        (H.Zhat t.f t.f' ∈ c1 ↔ ∃ s ∈ S.St, S.Fr (c.dat d) (c.lat t.abelian₂) = s • C₂) := by
      intro d t ht
      rw [GlobalTheory.HL.PairingClass.mem_class_iff M hM H r k P hrank hrel d₁ d t₁ t ht₁ ht Y0 c1 hc1 hZ₁,
        ← orb, GlobalTheory.HL.AbsGenMass.fr_eq hM c d t ht, hC₁]
      constructor
      · rintro ⟨s, hs, A, A', a1, a2, a3, a4, a5⟩
        refine ⟨c.grp s, (hSt s).1 hs, ?_⟩
        rw [(cls _ _).2.2]
        refine ((cls _ _).2.1 (fun b => c.e (t.f b), fun b => c.e (t.f' b))
          ⟨A, A', fun i j => (a1 i j).1, fun i j => (a1 i j).2.1, a2, a3,
            fun i j => hth ▸ (a1 i j).2.2, fun j => ?_, fun j => ?_⟩).1
        · simp [a4, Coord.grp]
        · simp [a5, Coord.grp]
      · rintro ⟨s, hs, e⟩
        have hm := (cls (fun b => c.e (t.f b)) (fun b => c.e (t.f' b))).1
        rw [e, (cls _ _).2.2] at hm
        obtain ⟨A, A', a1, a1', a2, a3, a6, a4, a5⟩ := hm
        refine ⟨c.grp.symm s, (hSt _).2 (by simpa using hs), A, A',
          fun i j => ⟨a1 i j, a1' i j, hth ▸ a6 i j⟩, a2, a3, fun j => c.e.injective ?_,
          fun j => c.e.injective ?_⟩
        · refine (a4 j).trans ?_
          simp [Coord.grp]
        · refine (a5 j).trans ?_
          simp [Coord.grp]
    have hstab : ∀ δ : S.Datum, ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ Λ →
        (S.BBzero δ Λ ∧ ∃ s ∈ S.St, S.Fr δ Λ = s • C₂) →
        (S.BBzero δ (s • Λ) ∧ ∃ s' ∈ S.St, S.Fr δ (s • Λ) = s' • C₂) := by
      rintro δ h hh Λ hΛ ⟨hb, s, hs, e⟩
      refine ⟨(aS δ Λ hΛ h hh).2.2.2.2.2.2.2.1.2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
      rw [(aS δ Λ hΛ h hh).2.2.2.2.1, e, mul_smul]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun d => ?_
    rw [mul_left_comm]
    congr 1
    have e0 := conv (R.RT d.1) (fun t => ¬ LocNG.BBne (H := H) t ∧ H.Zhat t.f t.f' ∈ c1)
      (fun t => ENNReal.ofReal (LocNG.mu P t))
    beta_reduce at e0
    rw [e0, GlobalTheory.HL.AbsGenMass.sum_eq_mass hM c R d.1 _
      (fun Λ => S.BBzero (c.dat d.1) Λ ∧ ∃ s ∈ S.St, S.Fr (c.dat d.1) Λ = s • C₂) (hstab _) (fun t ht => by
        rw [(hT1 _ t ht).2.2, not_not, hclass _ t ht]),
      hC₂, GlobalTheory.HL.MassOrbit.mass_orbit_class M.L r k S _ _ hΛ₁t, ← hC₂]
    unfold Frames.nT
    congr 2
    refine Eq.trans ?_ (hbij.1.encard_image _)
    congr 1
    ext Λ'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hT, hB, hF⟩
      obtain ⟨⟨Λ, g, g', T, T'⟩, ht, rfl⟩ := hT2 d.1 Λ' hT
      have ht' := ht
      obtain ⟨h1, h2, ⟨n₀, hn₀, hg, hΛ⟩, ⟨n₀', hn₀', hg', hΛ'⟩, -⟩ := ht'
      dsimp only at h1 h2 hg hΛ hg' hΛ'
      subst h1 h2 hg hg'
      have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d.1 n₀ n₀' Λ).1 ⟨ht, hn₀, hn₀', hΛ, hΛ'⟩
      have hmem : ((fun b => c.grp n (S.f b)), (fun b => c.grp n' (S.f' b))) ∈
          S.frameCls (fun b => c.grp n₀ (S.f b)) (fun b => c.grp n₀' (S.f' b)) := by
        rw [← (GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW).2.2.1, hF, hC₂']
        have e1 : (fun b => c.grp n (S.f b)) = fun b => c.e (n (P.A.f b)) :=
          funext fun b => by rw [c.f_eq, CoordUnip.grp_apply]
        have e2 : (fun b => c.grp n' (S.f' b)) = fun b => c.e (n' (P.B.f b)) :=
          funext fun b => by rw [c.f'_eq, CoordUnip.grp_apply]
        rw [e1, e2]
        exact (cls _ _).1
      obtain ⟨m₂, hm₂, m₂', hm₂', e2, e2', hW2⟩ :=
        relift M.L r k S _ _ _ _ _ _ hW ((hN n).1 hn) ((hN' n').1 hn') hmem
      obtain ⟨n₂, rfl⟩ := c.grp.surjective m₂
      obtain ⟨n₂', rfl⟩ := c.grp.surjective m₂'
      have key := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d.1 n₂ n₂' Λ).2 hW2
      have q1 : (fun b => n (P.A.f b)) = fun b => n₂ (P.A.f b) := funext fun b => c.e.injective (by
        rw [← CoordUnip.grp_apply c n, ← CoordUnip.grp_apply c n₂, ← c.f_eq, e2])
      have q2 : (fun b => n' (P.B.f b)) = fun b => n₂' (P.B.f b) := funext fun b => c.e.injective (by
        rw [← CoordUnip.grp_apply c n', ← CoordUnip.grp_apply c n₂', ← c.f'_eq, e2'])
      refine ⟨Λ, ⟨?_, fun hb => ?_⟩, rfl⟩
      · rw [q1, q2]
        exact key.1
      · rw [q1, q2] at hb
        exact (hT1 _ _ key.1).2.2.1 hb hB
    · rintro ⟨Λ, ⟨ht, hb⟩, rfl⟩
      refine ⟨(hT1 _ _ ht).1, ?_, ?_⟩
      · by_contra hB
        exact hb ((hT1 _ _ ht).2.2.2 hB)
      · exact (GlobalTheory.HL.AbsGenMass.fr_eq hM c d.1 _ ht).trans hC₂'.symm

end GlobalTheory.HL.LocGenMass
