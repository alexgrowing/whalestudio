import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAwayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceAdeleRingNumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstCells

variable {D : D7}

theorem latO_mono' (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : latO S T LS LT Q ≤ latO S T LS LT P := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hvan, rest⟩
  exact ⟨α, hα, fun v hv => hvan v fun hq => hv (h v hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (h : ∀ v, Q v → P v) : Vac ψ S T LS LT Q f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono' S T _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono' S T _ _ h hu) hh⟩

theorem theta_smul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi γ w]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

theorem vac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    (c : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (c • f) := by
  have e : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
    intro u; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  exact ⟨theta_smul' c hf.1, fun u hu => by rw [e, hf.2.1 u hu], fun e' he u hu hh => by rw [e, hf.2.2 e' he u hu hh]⟩

theorem comb_smul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem mem_cong {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, mem_cong]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_inf_le (V : HSp D) (P P' : Pl D → Prop) :
    grpOff V P ⊓ grpOff V P' ≤ grpOff V (fun p => P p ∨ P' p) := by
  intro g hg
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  rw [grpOff, mem_cong] at h1 h2 ⊢
  intro i j
  have a1 := h1 i j
  have a2 := h2 i j
  rw [idOff, Ideal.mem_iInf] at a1 a2 ⊢
  rintro ⟨w, hw | hw⟩
  · exact a1 ⟨w, hw⟩
  · exact a2 ⟨w, hw⟩

theorem exists_level (D : D7) (V : HSp D) (N : Lat V) (A B : Finset (Pl D)) (JA JB : Subgroup (GA D V)) (b : GA D V)
    (hAB : Disjoint B A) (hN : IsSelfDualC V N) (hb : b ∈ GfC V) (hA : JA ≤ grpAt V (· ∈ A)) (hAc : IsCompact (JA : Set (GA D V)))
    (hAo : IsOpen ((JA.subgroupOf (grpAt V (· ∈ A)) : Subgroup _) : Set (grpAt V (· ∈ A)))) (hB : JB ≤ grpAt V (· ∈ B))
    (hBc : IsCompact (JB : Set (GA D V)))
    (hBo : IsOpen ((JB.subgroupOf (grpAt V (· ∈ B)) : Subgroup _) : Set (grpAt V (· ∈ B)))) :
    ∃ K : Subgroup (GA D V), K ≤ GfC V ∧ IsCompact (K : Set (GA D V)) ∧
      IsOpen ((K.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) ∧
      ∀ k, k ∈ K ↔ ∃ κ x y, InK V N (fun p => p ∉ A ∧ p ∉ B) κ ∧ x ∈ JA ∧ y ∈ JB ∧ k = b⁻¹ * (κ * x * y) * b := by
  first
  | exact @_root_.GlobalTheory.CompactOpenIntegers.exists_level
  | exact _root_.GlobalTheory.CompactOpenIntegers.exists_level
  | (apply _root_.GlobalTheory.CompactOpenIntegers.exists_level <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactOpenIntegers.exists_level <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactOpenIntegers.exists_level <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactOpenIntegers.exists_level ..)

theorem split_off (D : D7) (V : HSp D) (A B : Finset (Pl D)) (hAB : Disjoint B A) (z : GA D V)
    (hz : z ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B)) :
    ∃ a ∈ GinfC V, ∃ x ∈ grpAt V (· ∈ A), ∃ y ∈ grpAt V (· ∈ B), z = a * y * x := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨-, -, hf1, hf2, -, ⟨e', he'⟩, hO, hI, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V B
  have h1 := he (e.symm z)
  rw [e.apply_symm_apply] at h1
  have h2 := he' (e'.symm (e.symm z).2)
  rw [e'.apply_symm_apply] at h2
  generalize e'.symm (e.symm z).2 = p at h2
  generalize e.symm z = q at h1 h2
  obtain ⟨⟨y, hy⟩, ⟨x, hx⟩⟩ := p
  obtain ⟨⟨a, ha⟩, ⟨f, hf⟩⟩ := q
  dsimp only at h1 h2
  subst h2
  refine ⟨a, ha, x, ?_, y, hy, by rw [h1, mul_assoc]⟩
  have hxo : x ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B) := by
    have : x = y⁻¹ * (a⁻¹ * z) := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem (hO _ _ (fun p hp h => h.2 hp) hy)) (mul_mem (inv_mem (real_le_off V _ ha)) hz)
  have hxB : x ∈ grpOff V (· ∈ B) := hO _ _ (fun p hp h => hp h) hx
  have hx' : x ∈ GfC V ⊓ grpOff V (fun p => (p ∉ A ∧ p ∉ B) ∨ p ∈ B) :=
    ⟨hf2 hx, grpOff_inf_le V _ _ ⟨hxo, hxB⟩⟩
  rw [hI] at hx'
  have hP : (fun p => ¬ ((p ∉ A ∧ p ∉ B) ∨ p ∈ B)) = (· ∈ A) := by
    funext p
    have := fun h : p ∈ B => Finset.disjoint_left.1 hAB h
    apply propext
    tauto
  rwa [hP] at hx'

theorem comm_at (D : D7) (V : HSp D) (A B : Finset (Pl D)) (hAB : Disjoint B A) {x y : GA D V} (hx : x ∈ grpAt V (· ∈ A))
    (hy : y ∈ grpAt V (· ∈ B)) : y * x = x * y := by
  obtain ⟨-, -, -, -, hcm, -, hO, hI, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V B
  refine hcm y hy x ?_
  have hx' : x ∈ GfC V ⊓ grpOff V (· ∈ B) :=
    ⟨(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V A).2.2.1 hx, hO _ _ (fun p hp h => Finset.disjoint_left.1 hAB h hp) hx⟩
  rwa [hI] at hx'

set_option maxHeartbeats 800000 in

theorem locFin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → OffLaw v w → GSupp (t := t) v → QFin v w → t.LocFin := by
  classical
  intro D c v t w hc hv ht hF hO hG hQ j σ h P₁ P₂
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  obtain ⟨KQ, TQ, hKQ, hKQc, hKQo, hTQ, hKQlaw, hTQsupp⟩ := hQ j σ h
  obtain ⟨hJG, hJGc, hJGo⟩ := hv.JG (j + 1) hj1
  obtain ⟨K, hKf, hKc, hKo, hKmem⟩ := exists_level D (c.V (j + 1)) (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) KQ
    (v.b (j + 1)) hF.disjG (hv.sd (j + 1) hj1) (hv.b (j + 1)) hJG hJGc hJGo hKQ hKQc hKQo
  have hone : InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) 1 := ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩

  have VGQ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q
  have VGG := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) v.gP
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp hg => Finset.disjoint_left.1 hF.disjG hp hg
  have hGQ : ∀ p, p ∈ v.gP → ¬ p ∈ w.Q := fun p hg hp => hQG p hp hg
  have hQoff : ∀ p, p ∈ w.Q → ¬ offP v w p := fun p hp h' => h'.2 hp
  have hGoff : ∀ p, p ∈ v.gP → ¬ offP v w p := fun p hp h' => h'.1 hp
  have hoffQ : ∀ p, offP v w p → ¬ p ∈ w.Q := fun p h' => h'.2
  have hoffG : ∀ p, offP v w p → ¬ p ∈ v.gP := fun p h' => h'.1
  have hQf : grpAt (c.V (j + 1)) (· ∈ w.Q) ≤ GfC _ := VGQ.2.2.1
  have hGf : grpAt (c.V (j + 1)) (· ∈ v.gP) ≤ GfC _ := VGG.2.2.1
  have gO : ∀ (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → grpAt (c.V (j + 1)) P ≤ grpOff (c.V (j + 1)) P' :=
    VGQ.2.2.2.2.2.2.1

  have W1 := (t.sBF j (σ + 1) h).weil
  rw [(ht.sBF j (σ + 1) h).1] at W1
  have W2 := (t.sFB j σ h).weil
  rw [(ht.sFB j σ h).1] at W2

  have hΨ1 := hv.Ψ j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
  have hΨ2 := hv.Ψ (j + 1) hj2 P₂ 1 (one_mem _) 1 (one_mem _)
  have VC1 := fun P P' hPP' => GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hPP'
  have VC2 := fun P P' hPP' => GlobalTheory.DisjComb.main D c.ψ hc.std (c.V (j + 1)) (c.V (j + 1 + 1)) P P' hPP'
  obtain ⟨hG1, -, -⟩ := hv.atG j
  obtain ⟨hG2, -, -⟩ := hv.atG (j + 1)
  obtain ⟨hQ1, -, -⟩ := hF.atQ j
  obtain ⟨hQ2, -, -⟩ := hF.atQ (j + 1)
  refine ⟨K, TQ.image (· * v.b (j + 1)), hKf, hKc, hKo, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hq
    exact mul_mem (hQf (hTQ q' hq')) (hv.b (j + 1))
  · intro k hk
    obtain ⟨κ, x, y, hκ, hx, hy, rfl⟩ := (hKmem k).1 hk
    obtain ⟨ax, hax, hx1, hx2, -⟩ := hF.lawG j hj1 x hx
    obtain ⟨ay, hay, hyl⟩ := hKQlaw y hy
    have hΨ1Q := vac_mono (Q := (· ∈ w.Q)) hΨ1 fun _ _ => trivial
    have hΨ2Q := vac_mono (Q := (· ∈ w.Q)) hΨ2 fun _ _ => trivial
    have hΨ1G := vac_mono (Q := (· ∈ v.gP)) hΨ1 fun _ _ => trivial
    have hΨ2G := vac_mono (Q := (· ∈ v.gP)) hΨ2 fun _ _ => trivial
    have hΨ1O := vac_mono (Q := offP v w) hΨ1 fun _ _ => trivial
    have hΨ2O := vac_mono (Q := offP v w) hΨ2 fun _ _ => trivial
    obtain ⟨hy1, hy2⟩ := hyl _ _ hΨ1Q hΨ2Q
    have hκG : κ ∈ grpOff _ (· ∈ v.gP) := gO _ _ hoffG hκ.1
    have hκQ : κ ∈ grpOff _ (· ∈ w.Q) := gO _ _ hoffQ hκ.1
    have hyG : y ∈ grpOff _ (· ∈ v.gP) := gO _ _ hQG (hKQ hy)
    have hθ1 : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) :=
      (((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨ1G).1
    have hθ2 : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) :=
      (((VC2 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ2).2 _ _ _ hΨ2G).1
    have hV1 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) :=
      ((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨ1G
    have hV2 : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) :=
      ((VC2 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ2).2 _ _ _ hΨ2G
    have hO1 := hO j σ h _ _ hΨ1O hΨ2O

    have L1 : t.om j (1, κ * x * y) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1))) =
        (ax * ay)⁻¹ • comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1)) := by
      have e : ((1 : GA D (c.V j)), κ * x * y) = (1, κ) * (1, x) * (1, y) := by simp
      rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [(VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 1 (one_mem _) y hyG _ hθ1, hy1,
        comb_smul', map_smul, hx1 _ hV1, map_smul, map_smul, smul_smul,
        (VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 1 (one_mem _) κ hκG _ hθ1,
        (VC1 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hQ1 1 (one_mem _) κ hκQ _ hΨ1.1,
        ((hO1.1 κ hκ).1), mul_inv, mul_comm]
    have L2 : t.om (j + 1) (κ * x * y, 1) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1))) =
        (ax * ay) • comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1)) := by
      have e : (κ * x * y, (1 : GA D (c.V (j + 1 + 1)))) = (κ, 1) * (x, 1) * (y, 1) := by simp
      rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [(VC2 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hG2 y hyG 1 (one_mem _) _ hθ2, hy2,
        comb_smul', map_smul, hx2 hj2 _ hV2, map_smul, map_smul, smul_smul,
        (VC2 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hG2 κ hκG 1 (one_mem _) _ hθ2,
        (VC2 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W2 _ hQ2 κ hκQ 1 (one_mem _) _ hΨ2.1,
        ((hO1.1 κ hκ).2), mul_comm]

    have vf1 := hF.vf j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
    have vf2 := hF.vf (j + 1) hj2 P₂ 1 (one_mem _) 1 (one_mem _)
    simp only [one_mul] at vf1 vf2
    have pt1 : t.pt j P₁ = t.om j ((v.b j)⁻¹, (v.b (j + 1))⁻¹) (w.sc j • comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P₁ 1 1))) := by
      rw [← vf1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk,
        map_one, Module.End.one_apply]
    have pt2 : t.pt (j + 1) P₂ = t.om (j + 1) ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹)
        (w.sc (j + 1) • comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) (v.Ψ (j + 1) P₂ 1 1))) := by
      rw [← vf2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk,
        map_one, Module.End.one_apply]
    refine ⟨ax * ay, mul_ne_zero hax hay, ?_, ?_⟩
    · rw [pt1, ← Module.End.mul_apply, ← map_mul]
      have e : ((1 : GA D (c.V j)), (v.b (j + 1))⁻¹ * (κ * x * y) * v.b (j + 1)) * ((v.b j)⁻¹, (v.b (j + 1))⁻¹) =
          ((v.b j)⁻¹, (v.b (j + 1))⁻¹) * (1, κ * x * y) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_assoc, mul_inv_cancel]
      rw [e, map_mul, Module.End.mul_apply, map_smul, L1, smul_comm, map_smul]
    · rw [pt2, ← Module.End.mul_apply, ← map_mul]
      have e : ((v.b (j + 1))⁻¹ * (κ * x * y) * v.b (j + 1), (1 : GA D (c.V (j + 1 + 1)))) *
          ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹) = ((v.b (j + 1))⁻¹, (v.b (j + 1 + 1))⁻¹) * (κ * x * y, 1) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_assoc, mul_inv_cancel]
      rw [e, map_mul, Module.End.mul_apply, map_smul, L2, smul_comm, map_smul]
  · intro α g hg h₁ hne
    obtain ⟨he, heQ⟩ := hF.e j α
    rw [he] at hg
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    obtain ⟨-, -, hrf, -⟩ := GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1))
    have gO0 : ∀ (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → grpAt (c.V j) P ≤ grpOff (c.V j) P' :=
      (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) w.Q).2.2.2.2.2.2.1
    have hεG : ε ∈ grpOff _ (· ∈ v.gP) := gO0 _ _ hQG (heQ ε hε)
    have hεO : ε ∈ grpOff _ (offP v w) := gO0 _ _ hQoff (heQ ε hε)
    have omm : ∀ (a a' : GA D (c.V j)) (b b' : GA D (c.V (j + 1))) f, t.om j (a, b) (t.om j (a', b') f) = t.om j (a * a', b * b') f :=
      fun a a' b b' f => by rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

    have vf1 := hF.vf j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
    rw [one_mul, one_mul, ← comb_smul', ← comb_smul'] at vf1
    have hΨ := vac_smul (w.sc j) hΨ1
    generalize w.sc j • v.Ψ j P₁ 1 1 = Ψ at vf1 hΨ
    obtain ⟨x, rfl⟩ : ∃ x, h₁ = x * v.b (j + 1) := ⟨h₁ * (v.b (j + 1))⁻¹, by group⟩
    rw [← omm, vf1] at hne
    have hΨQ := vac_mono (Q := (· ∈ w.Q)) hΨ fun _ _ => trivial
    have hΨG := vac_mono (Q := (· ∈ v.gP)) hΨ fun _ _ => trivial
    have hΨO := vac_mono (Q := offP v w) hΨ fun _ _ => trivial
    have hΨ2G := vac_mono (Q := (· ∈ v.gP)) hΨ2 fun _ _ => trivial
    have hΨ2O := vac_mono (Q := offP v w) hΨ2 fun _ _ => trivial
    have hVG : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb c.ψ _ _ (w.eQ j) Ψ) :=
      ((VC1 (· ∈ w.Q) (· ∈ v.gP) hQG).2.1 _ hQ1).2 _ _ _ hΨG
    have hVQ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) (comb c.ψ _ _ (v.eG j) Ψ) :=
      ((VC1 (· ∈ v.gP) (· ∈ w.Q) hGQ).2.1 _ hG1).2 _ _ _ hΨQ
    have hVO : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) :=
      ((VC1 (· ∈ v.gP) (offP v w) hGoff).2.1 _ hG1).2 _ _ _ (((VC1 (· ∈ w.Q) (offP v w) hQoff).2.1 _ hQ1).2 _ _ _ hΨO)

    obtain ⟨r, hr, hrO, z, hz, κ, hκ, rfl⟩ := (hO j σ h _ _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVO hεO (one_mem _)) hΨ2O).2.2.1 x
      (by rwa [omm, one_mul, mul_one])
    have hfix := ((hO j σ h _ _ hVO hΨ2O).1 κ hκ).1
    have hne2 : flatBF (t.sBF j (σ + 1) h) (t.om j (ε, z) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ))) ≠ 0 := by
      intro h0
      have hR := (GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant D c.ψ (offP v w)).1 (σ + 1) _ _ (t.sBF j (σ + 1) h) _ (W1.om_pres (ε, z) _ hVO.1) r hr hrO
      rw [(ht.sBF j (σ + 1) h).1] at hR
      apply hne
      have e := hR.2 h0
      have e' : t.om j (ε, r * z * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) =
          t.om j (1, r) (t.om j (ε, z) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ))) := by
        conv_rhs => rw [← hfix]
        rw [omm, omm, one_mul, mul_one]
      rw [e']
      exact e
    obtain ⟨a, ha, xG, hxG, xQ, hxQ, rfl⟩ := split_off D _ v.gP w.Q hF.disjG z hz
    have cQG : ∀ {x y}, x ∈ grpAt (c.V (j + 1)) (· ∈ v.gP) → y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q) → y * x = x * y :=
      fun hx hy => comm_at D _ v.gP w.Q hF.disjG hx hy

    have haQ : a * xQ ∈ grpOff _ (· ∈ v.gP) := mul_mem (real_le_off _ _ ha) (gO _ _ hQG hxQ)
    obtain ⟨rG, hrG, hrGa, kG, hkG, hxG'⟩ := (hG j σ h _ _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVG hεG haQ) hΨ2G).1 xG hxG (by
      rw [← (VC1 (· ∈ v.gP) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hG1 ε hεG _ haQ _ hVG.1, omm, one_mul,
        ← mul_assoc, ← hrf a ha xG (hGf hxG), mul_assoc, ← cQG hxG hxQ, ← mul_assoc]
      exact hne2)

    have haG : a * xG ∈ grpOff _ (· ∈ w.Q) := mul_mem (real_le_off _ _ ha) (gO _ _ hGQ hxG)
    obtain ⟨rQ, hrQ, hrQa, q, hq, kQ, hkQ, hxQ'⟩ := hTQsupp _ (GlobalTheory.OffPlaceWeil.vac_off W1 hVQ (one_mem _) haG) α ε hε xQ hxQ (by
      rw [← (VC1 (· ∈ w.Q) (fun _ => False) (fun _ _ h => h)).2.2.1 _ _ _ W1 _ hQ1 1 (one_mem _) _ haG _ hVQ.1, omm, mul_one,
        ← mul_assoc, ← hrf a ha xQ (hQf hxQ), ← (VC1 (· ∈ v.gP) (· ∈ w.Q) hGQ).1 _ _ hG1 hQ1]
      exact hne2)
    refine ⟨q * v.b (j + 1), Finset.mem_image_of_mem _ hq, r * rG * rQ, mul_mem (mul_mem hr hrG) hrQ, a, ha,
      (v.b (j + 1))⁻¹ * (kG * kQ * κ) * v.b (j + 1), ?_, ?_⟩
    · have m1 := (hKmem _).2 ⟨1, kG, kQ, hone, hkG, hkQ, rfl⟩
      have m2 := (hKmem _).2 ⟨κ, 1, 1, hκ, one_mem _, one_mem _, rfl⟩
      have m3 := mul_mem m1 m2
      have e : (v.b (j + 1))⁻¹ * (kG * kQ * κ) * v.b (j + 1) = (v.b (j + 1))⁻¹ * (1 * kG * kQ) * v.b (j + 1) *
          ((v.b (j + 1))⁻¹ * (κ * 1 * 1) * v.b (j + 1)) := by
        simp only [mul_assoc, mul_inv_cancel_left, one_mul, mul_one]
      rw [e]
      exact m3
    · have c1 : a * (rQ * q * kQ) * (rG * kG) = rG * rQ * a * q * (kG * kQ) := by
        rw [← hxQ', mul_assoc a xQ, ← mul_assoc xQ, cQG hrGa hxQ, ← mul_assoc a, ← mul_assoc a, hrf a ha rG (hGf hrGa), hxQ',
          ← cQG (hJG hkG) (hKQ hkQ), mul_assoc rG rQ a, ← hrf a ha rQ (hQf hrQa)]
        simp only [mul_assoc]
      rw [hxG', hxQ', c1]
      simp only [mul_assoc, mul_inv_cancel_left]

end GlobalTheory.FirstCells
