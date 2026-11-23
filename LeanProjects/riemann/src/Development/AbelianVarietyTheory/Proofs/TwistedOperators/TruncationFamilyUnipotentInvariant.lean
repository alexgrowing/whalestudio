import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab unipRad IsIsotropic diagH)
open scoped NNReal TensorProduct

noncomputable section

namespace GlobalTheory.TruncKer.RadInv

theorem iwAbs_mul_left_of_eq_one {G : Type} [Group G] {P : Subgroup G} {δ : P →* ℝ≥0} {K : Subgroup G}
    (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) (hp : δ p = 1) (g : G) :
    Doubling.iwAbs δ K (p * g) = Doubling.iwAbs δ K g := by
  by_cases hg : ∃ p' : P, ∃ k ∈ K, g = p' * k
  · obtain ⟨p', k, hk, rfl⟩ := hg
    rw [← mul_assoc, ← Subgroup.coe_mul, Doubling.iwAbs_mul_of_triv h _ hk, Doubling.iwAbs_mul_of_triv h _ hk,
      map_mul, hp, one_mul]
  · have hg' : ¬ ∃ p' : P, ∃ k ∈ K, (p : G) * g = p' * k := by
      rintro ⟨p', k, hk, e⟩
      exact hg ⟨p⁻¹ * p', k, hk, by rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
    unfold Doubling.iwAbs
    rw [dif_neg hg, dif_neg hg']

theorem below_invSV {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) {a b : SV k} (h : Below a b) :
    Below (invSV π ε a) (invSV π ε b) := fun i hi => congrArg _ (h _ (right_ne_zero_of_mul hi))

theorem below_single_stdVec {k : ℕ} {i j : Fin k} (h : i ≤ j) : Below (Pi.single i 1) (stdVec j) := fun t ht => by
  by_cases e : t = i
  · subst e; simp [stdVec, h]
  · exact absurd (Pi.single_eq_of_ne e _) ht

variable {D : D7} {V : HSp D}

theorem sub_mono (Φ : WittFrame V) {a b : SV (wittIndex V)} (h : Below a b) : Φ.sub a ≤ Φ.sub b :=
  Submodule.span_mono (Set.union_subset_union
    (Set.image_mono fun i (hi : a i = 1) => show b i = 1 from (h i (by rw [hi]; decide)).trans hi)
    (Set.image_mono fun i (hi : a i = -1) => show b i = -1 from (h i (by rw [hi]; decide)).trans hi))

theorem sub_single_le (Φ : WittFrame V) (i : Fin (wittIndex V)) :
    Φ.sub (Pi.single i 1) ≤ Submodule.span D.host.E {Φ.e i} := by
  refine Submodule.span_le.2 (Set.union_subset ?_ ?_)
  · rintro _ ⟨t, ht, rfl⟩
    obtain rfl : t = i := by
      by_contra e
      simp [Pi.single_eq_of_ne e] at ht
    exact Submodule.mem_span_singleton_self _
  · rintro _ ⟨t, ht, rfl⟩
    exfalso
    by_cases e : t = i
    · subst e; simp at ht
    · simp [Pi.single_eq_of_ne e] at ht

theorem exists_ne_zero_mem_sub (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V)))
    (ε : Fin (wittIndex V) → SignTypeˣ) (i : Fin (wittIndex V)) :
    ∃ y ∈ Φ.sub (invSV π ε (Pi.single i 1)), y ≠ 0 := by
  have hv : invSV π ε (Pi.single i 1) (π.symm i) = ε (π.symm i) := by simp [invSV]
  have h0 := Units.ne_zero (ε (π.symm i))
  generalize ((ε (π.symm i) : SignTypeˣ) : SignType) = s at hv h0
  cases s with
  | zero => exact absurd rfl h0
  | pos => exact ⟨Φ.e (π.symm i), Submodule.subset_span (Or.inl ⟨_, hv, rfl⟩), Φ.linearIndependent_e.ne_zero _⟩
  | neg =>
    refine ⟨Φ.f (π.symm i), Submodule.subset_span (Or.inr ⟨_, hv, rfl⟩), fun h => ?_⟩
    have := Φ.ef (π.symm i) (π.symm i)
    rw [if_pos rfl, h] at this
    simp [HSpace.hD] at this

theorem ratAct_inv_apply (γ : GF V) (x : V.V) : ratAct D.sp.cm V γ⁻¹ (ratAct D.sp.cm V γ x) = x := by
  have e : γ⁻¹.1.1 * γ.1.1 = 1 := congrArg (fun g : GF V => g.1.1) (inv_mul_cancel γ)
  rw [ratAct, ratAct, ← LinearMap.comp_apply, ← Matrix.toLin_mul, e, Matrix.toLin_one]
  rfl

theorem act_rat_mem {γ : GF V} {A B : Submodule D.host.E V.V} (h : ∀ x ∈ A, ratAct D.sp.cm V γ x ∈ B)
    {y : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ extSub (F := D.host.F) V (AF D.host.F) A) :
    act D.sp.cm V (rat V γ) y ∈ extSub (F := D.host.F) V (AF D.host.F) B :=
  (Submodule.span_le (p := (extSub (F := D.host.F) V (AF D.host.F) B).comap
    (HA.mat (AF D.host.F) D.sp.cm.sig V.gram (rat V γ)).1.mulVecLin)).2 (by
      rintro _ ⟨x, hx, rfl⟩
      show act D.sp.cm V (diagH D.sp.cm.sig V.gram (AF D.host.F) γ) (coordR V (AF D.host.F) x) ∈
        extSub (F := D.host.F) V (AF D.host.F) B
      rw [act_diagH]
      exact coordR_mem V _ (h x hx)) hy

end GlobalTheory.TruncKer.RadInv
end

namespace GlobalTheory.TruncKer.RadInv

variable {D : D7} {V : HSp D}

theorem conj_mem_unipRad {γ : GF V} {A B : Submodule D.host.E V.V}
    (h1 : ∀ x ∈ A, ratAct D.sp.cm V γ x ∈ B) (h2 : ∀ x ∈ B, ratAct D.sp.cm V γ⁻¹ x ∈ A)
    {n : GA D V} (hn : n ∈ unipRad D.sp.cm V (AF D.host.F) A) :
    rat V γ * n * (rat V γ)⁻¹ ∈ unipRad D.sp.cm V (AF D.host.F) B := by
  have hi : (rat V γ)⁻¹ = rat V γ⁻¹ := (map_inv _ _).symm
  have hc : ∀ y, act D.sp.cm V (rat V γ) (act D.sp.cm V (rat V γ⁻¹) y) = y := fun y => by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
  have hc' : ∀ y, act D.sp.cm V (rat V γ⁻¹) (act D.sp.cm V (rat V γ) y) = y := fun y => by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, hn.1 _ (act_rat_mem h2 hy), hc]
  · have hz : act D.sp.cm V (rat V γ⁻¹) y ∈ extSub (F := D.host.F) V (AF D.host.F) (perp V A) :=
      (mem_extSub_perp D.sp.cm V).2 fun x hx => by
        have := (hR_act D.sp.cm V (rat V γ⁻¹) (act D.sp.cm V (rat V γ) x) y).trans
          ((mem_extSub_perp D.sp.cm V).1 hy _ (act_rat_mem h1 hx))
        rwa [hc'] at this
    have := act_rat_mem h1 (hn.2 _ hz)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, hc] at this
    rwa [hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul]

theorem absChi_eq_one_of_mem_unip (Φ : WittFrame V) (p : PA Φ.flag0)
    (hp : (p : GA D V) ∈ Φ.flag0.unip D.sp.cm (AF D.host.F)) (i : Fin (wittIndex V)) : absChi Φ i p = 1 := by
  have he : Φ.e i ∈ Φ.flag0.X i.succ := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  have h1 := Φ.coef_eq_zero D.sp.cm (AF D.host.F) i ((IsoFlag.mem_unip_iff.1 hp).1 i _ he)
  rw [map_sub, sub_eq_zero, WittFrame.coef_coordR, Φ.ef, if_pos rfl, map_one] at h1
  have h2 : Φ.chi D.sp.cm (AF D.host.F) i p = 1 := h1
  have h3 : (Φ.chi D.sp.cm (AF D.host.F) i).toHomUnits p = 1 := Units.ext h2
  simp only [absChi, MonoidHom.comp_apply, h3, map_one]

theorem ratAct_inv_e_mem (Φ : WittFrame V) {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ}
    {w : GF V} (hw : Φ.IsWeylRep D.sp.cm π ε w) {i j : Fin (wittIndex V)} (hij : i ≤ j) :
    ratAct D.sp.cm V w⁻¹ (Φ.e i) ∈ Φ.sub (invSV π ε (stdVec j)) := by
  obtain ⟨y, hy, hy0⟩ := exists_ne_zero_mem_sub Φ π ε i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (sub_single_le Φ i (hw _ y hy))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hy0 (by rw [← ratAct_inv_apply w y, ← hc, map_zero])
  have e : Φ.e i = ratAct D.sp.cm V w (c⁻¹ • y) := by
    rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e, ratAct_inv_apply]
  exact sub_mono Φ (below_invSV π ε (below_single_stdVec hij)) (Submodule.smul_mem _ _ hy)

end GlobalTheory.TruncKer.RadInv

namespace GlobalTheory.TruncKer

open RadInv in

theorem yfam_unipRad_mul : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ Q, IsPar Q → ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ x Tr,
    Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (n * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q := by
  intro D V Φ L a hg Q hQ u hu hW n hn x Tr
  obtain ⟨π, ε, w, hw, hsub, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQ
  rw [hY, hY]
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hsub hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  have hX : IsIsotropic V (Φ.flag0.X j.succ) := Φ.flag0.isIsotropic (Fin.succ_ne_zero j)
  have h1 : ∀ y ∈ Φ.sub (invSV π ε (stdVec j)), ratAct D.sp.cm V w y ∈ Φ.flag0.X j.succ := fun y hy =>
    Φ.sub_stdVec j ▸ hw _ y hy
  have h2 : ∀ y ∈ Φ.flag0.X j.succ, ratAct D.sp.cm V w⁻¹ y ∈ Φ.sub (invSV π ε (stdVec j)) := by
    intro y hy
    refine (Submodule.span_le (p := (Φ.sub (invSV π ε (stdVec j))).comap (ratAct D.sp.cm V w⁻¹))).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact ratAct_inv_e_mem Φ hw (show i ≤ j from Nat.lt_succ_iff.1 hi)
  have hN : rat V w * n * (rat V w)⁻¹ ∈ (IsoFlag.single hX).unip D.sp.cm (AF D.host.F) := by
    rw [IsoFlag.unip_single]
    exact conj_mem_unipRad h1 h2 (by rw [← IsoFlag.unip_single]; exact hn)
  have hU := Φ.flag0.unip_single_le D.sp.cm (AF D.host.F) (Fin.succ_ne_zero j) hN
  let p : PA Φ.flag0 := ⟨_, Φ.flag0.unip_le_par _ _ hU⟩
  have hK := hg.isCompact
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  have e : rat V w * (n * x) = (p : GA D V) * (rat V w * x) := by simp [p, mul_assoc]
  have key : H0 Φ (levelAll D.sp.cm.sig V.gram L a) (rat V w * (n * x)) =
      H0 Φ (levelAll D.sp.cm.sig V.gram L a) (rat V w * x) := by
    simp only [H0, e]
    congr 2
    funext i
    rw [iwAbs_mul_left_of_eq_one (Doubling.triv_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hK) p
      (absChi_eq_one_of_mem_unip Φ p hU i)]
  simp only [Ys, key]

end GlobalTheory.TruncKer
