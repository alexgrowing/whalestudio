import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SlopeDesc

open Filter
open scoped ENNReal

section Generic

open GlobalTheory.CompHt

theorem rank_eq_of_coord {K K' V V' : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K' V'] (ι : K →+* K') (φ : V →ₛₗ[ι] V') {d : ℕ} (b : Fin d → K')
    (hb : ∀ x : K', ∃ a : Fin d → K, x = ∑ j, ι (a j) * b j)
    (hs : ∀ v', ∃ g : Fin d → V, v' = ∑ j, b j • φ (g j))
    (hi : ∀ g : Fin d → V, ∑ j, b j • φ (g j) = 0 → ∀ j, g j = 0) : Module.rank K' V' = Module.rank K V := by
  classical
  let v := Module.Basis.ofVectorSpace K V
  have h1 : LinearIndependent K' fun i => φ (v i) := by
    rw [linearIndependent_iff']
    intro s x hx i hi'
    choose a ha using fun i => hb (x i)
    have h2 := hi (fun j => ∑ i ∈ s, a i j • v i) (by
      rw [← hx]
      simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm])
    rw [ha i]
    exact Finset.sum_eq_zero fun j _ => by
      rw [linearIndependent_iff'.1 v.linearIndependent s _ (h2 j) i hi', map_zero, zero_mul]
  have h2 : ⊤ ≤ Submodule.span K' (Set.range fun i => φ (v i)) := fun v' _ => by
    obtain ⟨g, rfl⟩ := hs v'
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    rw [← v.linearCombination_repr (g j), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← (Module.Basis.mk h1 h2).mk_eq_rank'', ← v.mk_eq_rank'']

theorem logCard_pow (m : ℕ∞) {d : ℕ} (hd : d ≠ 0) : logCard (m ^ d) = d * logCard m := by
  induction m using ENat.recTopCoe with
  | top => rw [ENat.top_pow hd, logCard_top, ENNReal.mul_top (Nat.cast_ne_zero.2 hd)]
  | coe m => rw [← Nat.cast_pow, logCard_coe, logCard_coe, Nat.cast_pow, Real.log_pow,
      ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]

theorem countVol_le_of_pow (D n a : ℕ) {d : ℕ} (hd : d ≠ 0) {m m' : ℕ → ℕ∞}
    (h : ∀ᶠ k in atTop, m' (a * k) ≤ m (a * k) ^ d) : countVol D (n * d) a m' ≤ countVol D n a m := by
  refine limsup_le_limsup (h.mono fun k hk => ?_)
  have h1 : logCard (m' (a * k)) ≤ d * logCard (m (a * k)) := by
    rw [← logCard_pow _ hd]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 hk))
  refine (ENNReal.div_le_div_right (mul_le_mul_right h1 _) _).trans_eq ?_
  rw [mul_left_comm, Nat.cast_mul n, mul_comm (n : ℝ≥0∞), mul_assoc,
    ENNReal.mul_div_mul_left _ _ (Nat.cast_ne_zero.2 hd) (ENNReal.natCast_ne_top d)]

theorem le_volSlope_of_shift {δ : ℝ} {vol vol' : ℝ → ℝ≥0∞} (h : ∀ t ε : ℝ, 0 < ε → vol' t ≤ vol (t + ε)) {s : ℝ}
    (hs : (s : EReal) ≤ volSlope δ vol') : (s : EReal) ≤ volSlope δ vol := by
  refine le_iInf fun t => ?_
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t)), ← EReal.coe_add]
  refine le_of_forall_lt fun x hx => ?_
  obtain ⟨y, hxy, hy⟩ := EReal.lt_iff_exists_real_btwn.1 hx
  have hy' : y < s + t := EReal.coe_lt_coe_iff.1 hy
  have h1 := (hs.trans (iInf_le _ (y - s)))
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    add_sub_cancel] at h1
  refine hxy.trans_le (h1.trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 (ENNReal.div_le_div_right ?_ _)))
  simpa using h (y - s) (s + t - y) (by linarith)

theorem encard_le_pow {α β : Type} {S : Set α} {T : Set β} {d : ℕ} (g : α → Fin d → β) (hg : Set.InjOn g S)
    (hT : ∀ x ∈ S, ∀ j, g x j ∈ T) : S.encard ≤ T.encard ^ d := by
  let φ : S → (Fin d → T) := fun x j => ⟨g x j, hT x x.2 j⟩
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hg x.2 y.2 (funext fun j =>
    congrArg Subtype.val (congrFun h j)))
  have := ENat.card_le_card_of_injective hφ
  refine this.trans_eq ?_
  simp only [Set.encard, ENat.card, Cardinal.mk_pi, Cardinal.prod_const, Cardinal.lift_id, Cardinal.mk_fin,
    Cardinal.lift_natCast, Cardinal.power_natCast, map_pow, Cardinal.lift_uzero]

theorem exists_dual (K K' : Type) [Field K] [Field K'] [NumberField K] [NumberField K'] [Algebra K K'] :
    ∃ (d N : ℕ) (B : Module.Basis (Fin d) K K') (bs : Fin d → K'), d ≠ 0 ∧ N ≠ 0 ∧
      Module.finrank ℚ K' = Module.finrank ℚ K * d ∧ (∀ j, IsIntegral ℤ (bs j)) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], ∃ (n : ℕ) (s : Fin n → (K' →ₐ[K] Ω)),
        ∀ i j, ∑ k, s k (bs j) * s k (B i) = if i = j then (N : Ω) else 0 := by
  classical
  let B := Module.finBasis K K'
  let B' := B.traceDual
  obtain ⟨N, hN⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image B')
  refine ⟨_, N.natAbs, B, fun j => (N.natAbs : K') * B' j, Module.finrank_pos.ne', Int.natAbs_ne_zero.2 hN.1,
    (Module.finrank_mul_finrank ℚ K K').symm, fun j => ?_, fun Ω _ _ _ => ?_⟩
  · have := hN.2 (B' j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rw [zsmul_eq_mul] at this
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice N with h | h <;> rw [h]
    · exact this
    · simpa using this.neg
  · let e := (Fintype.equivFin (K' →ₐ[K] Ω)).symm
    refine ⟨_, e, fun i j => ?_⟩
    rw [e.sum_comp fun s => s ((N.natAbs : K') * B' j) * s (B i)]
    have := trace_eq_sum_embeddings Ω (K := K) (x := B' j * B i)
    rw [Module.Basis.trace_traceDual_mul] at this
    simp only [map_mul, map_natCast, mul_assoc, ← Finset.mul_sum] at this ⊢
    rw [← this]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]

end Generic

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct GlobalTheory.SecFieldChange GlobalTheory.AllWt GlobalTheory.FieldBC
  GlobalTheory.FieldBCModel GlobalTheory.CompHt GlobalTheory.FlatLine
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map evR_map
  map_cancel frBor_map hasBC_of)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def rulHom : Rul Xo c →+* Rul Xo c' where
  toFun := rulBC hle
  map_one' := rulBC_one hle
  map_zero' := funext fun p => funext fun y => by
    letI := resAlg hle p.R
    exact evalAt_zero _ _ (y.res hle (fun _ => rfl))
  map_mul' f g := funext fun p => funext fun y => by
    letI := resAlg hle p.R
    exact evalAt_mul _ _ f g (y.res hle (fun _ => rfl))
  map_add' f g := funext fun p => funext fun y => by
    letI := resAlg hle p.R
    exact evalAt_add _ _ f g (y.res hle (fun _ => rfl))

theorem rulBC_smul (a : c.F) (f : Rul Xo c) : rulBC hle (a • f) = incF c c' hle a • rulBC hle f :=
  funext fun p => funext fun y => by
    letI := resAlg hle p.R
    refine (evalAt_smul _ _ a f (y.res hle (fun _ => rfl))).trans ?_
    show _ = incF c c' hle a • rulBC hle f p y
    rw [Algebra.smul_def]
    rfl

theorem rulBC_mem_secZ {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e) :
    rulBC hle f ∈ GlobalTheory.AllWt.secZ Xo c' e := by
  refine ⟨rulBC_natural hle hf.1, fun p t y y' h => ?_⟩
  letI := resAlg hle p.R
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  exact GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Xo c e hf p.R t
    (y.res hle (fun _ => rfl)) (y'.res hle (fun _ => rfl)) h

include hle in

theorem nonempty_keySec_bc (h : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) : Nonempty (GlobalTheory.ShFam.KeySec Xo c') :=
  h.elim fun κ => ⟨⟨Units.map (rulHom hle).toMonoidHom κ.ρ, rulBC_mem_secZ hle κ.mem⟩⟩

theorem exists_coord [Algebra c.F c'.F] (halg : ∀ x, algebraMap c.F c'.F x = incF c c' hle x) {d : ℕ}
    (B : Module.Basis (Fin d) c.F c'.F) {e : Ix Dw → ℤ} {f' : Rul Xo c'} (hf' : f' ∈ GlobalTheory.AllWt.secZ Xo c' e) :
    ∃ fs : Fin d → Rul Xo c, (∀ j, fs j ∈ GlobalTheory.AllWt.secZ Xo c e) ∧ f' = ∑ j, B j • rulBC hle (fs j) := by
  classical
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hBC : HasBC Xo c := hasBC_of hS
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hA' := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c'
  have hov : ∀ p : TRing c.F, AlgOver c c' hle (Ext c.F c'.F p.R) := fun p x => by
    rw [← halg]; exact ext_tower x
  choose z hz using fun (p : TRing c.F) (y : FrPt Xo c p.R) => hBC p.R (Ext c.F c'.F p.R) (inR c'.F p.R) y
  have hT : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), FromT ((z p y).ext hle (hov p)) := fun p y => by
    haveI := ext_reduced (K' := c'.F) p
    exact hA' _ _
  obtain ⟨fs, hfs⟩ : ∃ fs : Fin d → Rul Xo c, ∀ j p y,
      fs j p y = crd (B.coord j) (evR Xo c' f' ((z p y).ext hle (hov p))) := ⟨fun j p y => _, fun _ _ _ => rfl⟩
  have hnat : ∀ j, Natural c (fs j) := by
    intro j p q ψ y w h
    have h' : FrMap ψ y w := h
    obtain ⟨Ψ, Ψ₀, e₁, e₂, e₃⟩ := exists_map (K' := c'.F) ψ
    have h0 := map_trans ψ (inR c'.F q.R) h' (hz q w)
    have h1 := map_cancel hBC e₂ (hz p y) h0
    have h2 := frMap_ext hle (hov p) (hov q) Ψ₀ Ψ e₁ h1
    rw [hfs, hfs, evR_map (wd c') hf'.1 (hT p y) h2, e₃]
  refine ⟨fs, fun j => ⟨hnat j, ?_⟩, ?_⟩
  · intro p t y y' h
    have h2 := frBor_ext hle (hov p) (frBor_map h (hz p y) (hz p y'))
    haveI := ext_reduced (K' := c'.F) p
    have h3 := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c' e hf' _ _ _ _ h2
    rw [hfs, hfs, h3, ← crd_mul]
    simp only [← map_zpow, ← map_prod]
    rfl
  · funext q y
    letI := resAlg hle q.R
    have h : AlgOver c c' hle q.R := fun _ => rfl
    obtain ⟨p, φ, y₀, hy₀'⟩ := fromT_res hle q h y
    have hy₀ : FrMap φ y₀ (y.res hle h) := hy₀'
    obtain ⟨Φ, Φ₀, e₁, e₂, e₃⟩ := exists_lift (K' := c'.F) (fun x => by rw [halg]; exact h x) φ
    have h1 := map_cancel hBC e₂ (hz p y₀) hy₀
    have h2 : FrMap Φ ((z p y₀).ext hle (hov p)) y := frMap_ext hle (hov p) h Φ₀ Φ e₁ h1
    rw [← evR_test hf'.1 q y, evR_map (wd c') hf'.1 (hT p y₀) h2, e₃ d B, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hfs, ← evR_of_map (wd c) (hnat j) hy₀, ← Algebra.smul_def]
    rfl

def evAlong {Ω : Type} [Field Ω] [Algebra c.F Ω] (s : c'.F →+* Ω) (hs : ∀ a, s (incF c c' hle a) = algebraMap c.F Ω a)
    (f' : Rul Xo c') (y : FrPt Xo c Ω) : Ω :=
  letI := s.toAlgebra
  evR Xo c' f' (y.ext hle hs)

theorem evR_coord {Ω : Type} [Field Ω] [Algebra c.F Ω] {d n N : ℕ} {b bs : Fin d → c'.F} {s : Fin n → (c'.F →+* Ω)}
    (hs : ∀ k a, s k (incF c c' hle a) = algebraMap c.F Ω a)
    (hd : ∀ i j, ∑ k, s k (bs j) * s k (b i) = if i = j then (N : Ω) else 0) {fs : Fin d → Rul Xo c}
    (hf : ∀ j, Natural c (fs j)) (j : Fin d) (y : FrPt Xo c Ω) :
    evR Xo c ((N : c.F) • fs j) y = ∑ k, s k (bs j) * evAlong hle (s k) (hs k) (∑ i, b i • rulBC hle (fs i)) y := by
  have h1 : ∀ k, evAlong hle (s k) (hs k) (∑ i, b i • rulBC hle (fs i)) y = ∑ i, s k (b i) * evR Xo c (fs i) y := fun k => by
    letI := (s k).toAlgebra
    refine (evR_sum_smul (c := c') (y.ext hle (hs k)) b _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [evR_rulBC hle (hf i) (hs k)]
    rfl
  simp only [h1, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hd, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (evalAt_smul _ _ _ _ y).trans (by rw [map_natCast]; rfl)

theorem eq_zero_of_algClosed {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω), evR Xo c g y = 0) : g = 0 := by
  refine secZ_eq_zero_of_genVal hg fun Z => ?_
  have h0 : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  let φ : Om Z →ₐ[c.F] AlgebraicClosure (Om Z) := IsScalarTower.toAlgHom _ _ _
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap φ (genFr h0 Z)
  have := h _ z
  rw [GlobalTheory.FlagTan.evR_frMap hg.1 hz] at this
  exact (map_eq_zero φ).1 this

theorem rulBC_idem (eC : Comp Xo c ≃ Comp Xo c')
    (h : ∀ Z : Comp Xo c, ∀ f ∈ sec Xo c 0 0, genVal (eC Z) (rulBC hle f) = 0 ↔ genVal Z f = 0) (Z : Comp Xo c) :
    rulBC hle (idem Z) = idem (eC Z) := by
  have hg : ∀ (c : Coeff l) (Z Z' : Comp Xo c), genVal Z' (idem Z) = if Z' = Z then 1 else 0 := fun c Z Z' => by
    have h0 := Reg.genFrEx_and_genFromTest E H Dw l Xo c
    split_ifs with e
    · subst e
      exact evR_idem (liesOn_genFr h0.1 Z') (h0.2 _ Z')
    · exact evC_eq_zero h0.1 e (idem_mem_suppOn Z)
  have hs : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← secZ_nat]
    congr 1
    funext i
    rcases i with _ | i <;> rfl
  refine sub_eq_zero.1 (secZ_eq_zero_of_genVal
    (Submodule.sub_mem _ (rulBC_mem_secZ hle (idem_mem_secZ Z)) (idem_mem_secZ _)) fun Z' => ?_)
  obtain ⟨Z', rfl⟩ := eC.surjective Z'
  rw [map_sub, hg]
  by_cases e : Z' = Z
  · subst e
    have h1 := (h Z' _ (hs ▸ Submodule.sub_mem _ (idem_mem_secZ Z') one_mem_secZ)).2 (by rw [map_sub, hg]; simp)
    have h2 : rulBC hle (idem Z' - 1) = rulBC hle (idem Z') - 1 := by
      exact ((rulHom hle).map_sub (idem Z') 1).trans (congrArg (_ - ·) (rulBC_one hle))
    rw [h2, map_sub, map_one] at h1
    rwa [if_pos rfl]
  · rw [if_neg (eC.injective.ne e), sub_zero]
    exact (h Z' _ (hs ▸ idem_mem_secZ Z)).2 (by rw [hg, if_neg e])

end GlobalTheory.SlopeDesc
