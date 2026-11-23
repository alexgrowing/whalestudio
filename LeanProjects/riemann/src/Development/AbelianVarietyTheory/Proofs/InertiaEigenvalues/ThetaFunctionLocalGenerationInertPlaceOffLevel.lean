import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacua
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.Inert

open GlobalTheory.Hk3

section Local

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
  {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
  {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
  {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

def vacSub (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) : Submodule ℂ M where
  carrier := {s | LocVac ρ s}
  add_mem' := by intro a b ha hb u hu; simp [ha u hu, hb u hu]
  zero_mem' := by intro u _; simp
  smul_mem' := by intro c a ha u hu; simp [ha u hu]

theorem exists_ext (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (φ : M →ₗ[ℂ] M) (hφ : ∀ s, φ s ∈ vacSub ρ) :
    ∃ B : Module.End ℂ M, ∀ x s, LocVac ρ s → B (ρ x s) = ρ x (φ s) := by
  obtain ⟨B, h1, h2⟩ := locPair_extend_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hp φ fun s _ => hφ s
  refine ⟨B, fun x s hs => ?_⟩
  rw [← h2 s hs]
  exact congrArg (fun F : Module.End ℂ M => F s) (h1 x)

theorem rel_transfer (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) {ι : Type} [Fintype ι] (x : ι → Matrix (Fin n') (Fin n) L)
    (t t' : ι → M) (ht : ∀ k, LocVac ρ (t k)) (ht' : ∀ k, LocVac ρ (t' k))
    (hr : ∀ a : ι → ℂ, ∑ k, a k • t k = 0 → ∑ k, a k • t' k = 0) (h0 : ∑ k, ρ (x k) (t k) = 0) :
    ∑ k, ρ (x k) (t' k) = 0 := by
  classical
  let T := Fintype.linearCombination ℂ t
  let T' := Fintype.linearCombination ℂ t'
  obtain ⟨r, hr'⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
  obtain ⟨S, hS⟩ := LinearMap.exists_extend r
  have hST : ∀ a, T' (S (T a)) = T' a := fun a => by
    rw [← sub_eq_zero, ← map_sub]
    refine hr _ ?_
    show T _ = 0
    have e1 : S (T a) = r ⟨T a, a, rfl⟩ := LinearMap.congr_fun hS ⟨T a, a, rfl⟩
    have e2 : T (r ⟨T a, a, rfl⟩) = T a := congrArg Subtype.val (LinearMap.congr_fun hr' ⟨T a, a, rfl⟩)
    rw [map_sub, e1, e2, sub_self]
  obtain ⟨B, hB⟩ := exists_ext hp (T' ∘ₗ S) fun s =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ht' k)
  have e : ∀ k, (T' ∘ₗ S) (t k) = t' k := fun k => by
    have := hST (Pi.single k 1)
    simpa [T, T'] using this
  have := congrArg B h0
  rw [map_sum, map_zero] at this
  simpa only [hB _ _ (ht _), e] using this

theorem exists_killed (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (𝒜 : Set (Module.End ℂ M))
    (h𝒜 : ∀ A ∈ 𝒜, ∀ x s, A (ρ x s) = ρ x (A s)) {ι : Type} [Fintype ι] (x : ι → Matrix (Fin n') (Fin n) L) (f : M)
    (hf : ∀ A ∈ 𝒜, A f = 0) (m : ℕ) : ∀ (W : Submodule ℂ M) [FiniteDimensional ℂ W], Module.finrank ℂ W = m → W ≤ vacSub ρ →
      ∀ t : ι → M, (∀ k, t k ∈ W) → ∑ k, ρ (x k) (t k) = f →
      ∃ t' : ι → M, (∀ k, LocVac ρ (t' k) ∧ ∀ A ∈ 𝒜, A (t' k) = 0) ∧ ∑ k, ρ (x k) (t' k) = f := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W _ hm hW t ht hs
  by_cases hk : ∀ A ∈ 𝒜, ∀ w ∈ W, A w = 0
  · exact ⟨t, fun k => ⟨hW (ht k), fun A hA => hk A hA _ (ht k)⟩, hs⟩
  push Not at hk
  obtain ⟨A, hA, w, hw, hne⟩ := hk
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ M, l (A w) = 1 := by
    have := (Module.forall_dual_apply_eq_zero_iff ℂ (A w)).not.mpr hne
    push Not at this
    obtain ⟨l, hl⟩ := this
    exact ⟨(l (A w))⁻¹ • l, by simp [hl]⟩
  obtain ⟨B, hB⟩ := exists_ext hp (l.smulRight w) fun s => Submodule.smul_mem _ _ (hW hw)
  have hAv : ∀ s, LocVac ρ s → LocVac ρ (A s) := fun s hs u hu => by rw [← h𝒜 A hA, hs u hu]
  have h0 : ∑ k, ρ (x k) (l (A (t k)) • w) = 0 := by
    have e := congrArg (fun z => B (A z)) hs
    simp only [hf A hA, map_zero, map_sum, h𝒜 A hA] at e
    rw [← e]
    exact Finset.sum_congr rfl fun k _ => (hB _ _ (hAv _ (hW (ht k)))).symm
  let W' : Submodule ℂ M := W ⊓ LinearMap.ker (l ∘ₗ A)
  have hlt : W' < W := lt_of_le_of_ne inf_le_left fun h => by
    have : w ∈ W' := h.symm ▸ hw
    have h2 : l (A w) = 0 := this.2
    exact one_ne_zero (hl.symm.trans h2)
  have : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hlt.le
  refine ih _ (hm ▸ Submodule.finrank_lt_finrank_of_lt hlt) W' rfl (hlt.le.trans hW)
    (fun k => t k - l (A (t k)) • w) (fun k => ⟨sub_mem (ht k) (W.smul_mem _ hw), ?_⟩) ?_
  · show l (A _) = 0
    rw [map_sub, map_sub, map_smul, map_smul, hl, smul_eq_mul, mul_one, sub_self]
  · simp only [map_sub, Finset.sum_sub_distrib, h0, hs, sub_zero]

theorem howe_killed (hH : HoweUnram) (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (𝒜 : Set (Module.End ℂ M))
    (h𝒜 : ∀ A ∈ 𝒜, ∀ x s, A (ρ x s) = ρ x (A s)) (f : M) (hf : ∀ A ∈ 𝒜, A f = 0)
    (hK : ∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) f = f) :
    f ∈ Submodule.span ℂ {φ | ∃ h s, LocVac ρ s ∧ (∀ A ∈ 𝒜, A s = 0) ∧ φ = ω (1, h) s} := by
  classical
  have hm : f ∈ Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧
      w = ρ x s} := by rw [hp.span]; trivial
  obtain ⟨N, c, g, hg⟩ := Submodule.mem_span_set'.1 hm
  choose x s hs hx using fun k => (g k).2
  have h1 : ∀ k, c k • s k ∈ vacSub ρ := fun k => Submodule.smul_mem _ _ (hs k)
  have := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun k => c k • s k)
  obtain ⟨t, ht, hsum⟩ := exists_killed hp 𝒜 h𝒜 x f hf _ (Submodule.span ℂ (Set.range fun k => c k • s k)) rfl
    (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h1 k)) (fun k => c k • s k)
    (fun k => Submodule.subset_span ⟨k, rfl⟩) (by rw [← hg]; exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hx])
  let W := Submodule.span ℂ (Set.range t)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range t)
  have hW : ∀ w ∈ W, LocVac ρ w ∧ ∀ A ∈ 𝒜, A w = 0 := fun w hw => by
    refine ⟨(Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (ht k).1) : W ≤ vacSub ρ) hw, fun A hA => ?_⟩
    exact (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (ht k).2 A hA) : W ≤ LinearMap.ker A) hw
  have htW : ∀ k, t k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  let b := Module.finBasis ℂ W
  choose l hl using fun j => LinearMap.exists_extend (b.coord j)
  have hl' : ∀ j k, l j (t k) = b.repr ⟨t k, htW k⟩ j := fun j k => LinearMap.congr_fun (hl j) ⟨t k, htW k⟩
  have e : f = ∑ j, ∑ k, ρ (x k) (l j (t k) • (b j : M)) := by
    rw [Finset.sum_comm, ← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_sum]
    congr 1
    have := congrArg Subtype.val (b.sum_repr ⟨t k, htW k⟩)
    simpa only [hl', Submodule.coe_sum, Submodule.coe_smul] using this.symm
  rw [e]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hb := hW _ (b j).2
  have hb0 : (b j : M) ≠ 0 := fun h => b.ne_zero j (Subtype.ext h)
  obtain ⟨B, hB⟩ := exists_ext hp ((l j).smulRight (b j : M)) fun s => Submodule.smul_mem _ _ hb.1
  have hone := (Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)).one_mem
  refine Submodule.span_mono ?_ ((howe_on_span hH hp _ hb0 hb.1).1 _ ?_ fun g hg => ?_)
  · rintro _ ⟨h, rfl⟩
    exact ⟨h, _, hb.1, hb.2, rfl⟩
  · refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hn : ∀ y, ∃ y', ∀ s, LocVac ρ s → ω (g, 1) (ρ y s) = ρ y' s := fun y =>
      ⟨_, fun s hs => (congrArg (fun F : Module.End ℂ M => F s) (hp.norm g 1 y)).trans
        (congrArg (ρ _) (hp.fix g 1 hg hone s hs))⟩
    choose mv hmv using hn
    have e1 : ∑ k, ρ (mv (x k)) (t k) = ∑ k, ρ (x k) (t k) := by
      rw [hsum, ← hK g hg, ← hsum, map_sum]
      exact Finset.sum_congr rfl fun k _ => (hmv _ _ (ht k).1).symm
    have e2 := congrArg B e1
    simp only [map_sum, hB _ _ (ht _).1, LinearMap.smulRight_apply] at e2
    rw [map_sum]
    exact (Finset.sum_congr rfl fun k _ => hmv _ _ ((vacSub ρ).smul_mem _ hb.1)).trans e2

end Local

section Global

open GlobalTheory.InertLoc GlobalTheory.SplitScalar GlobalTheory.FinWeilO

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem exists_pair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E) (hW : IsWeilDatumO ψ S T χS χT om)
    (hP : Formalism.DivisionValues.conjPl P = P) (hfix : VacFix ψ om P) (e : AE D) (he : IsPrimeIdem P e e) :
    ∃ (ϖ : LP D P) (σ : LP D P →+* LP D P) (q : ℕ) (δ : LP D P) (JS : GL (Fin S.rank) (LP D P)) (JT : GL (Fin T.rank) (LP D P))
      (ψ' : AddChar (LP D P) ℂ) (ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D P) → Module.End ℂ (thetaSub ψ S T))
      (ω : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (LP D P)) ×
        Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (LP D P)) →* Module.End ℂ (thetaSub ψ S T))
      (ιS : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (LP D P)) →* GA D S)
      (ιT : Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (LP D P)) →* GA D T)
      (κ : Matrix (Fin T.rank) (Fin S.rank) (LP D P) → WO S T), LocPair ϖ σ q δ JS JT ψ' ρ ω ∧
      (∀ g, ιS g ∈ hyp S P ↔ (g : GL (Fin S.rank) (LP D P)) ∈ Formalism.UG.GLint (Fin S.rank) (Formalism.UG.intL _)) ∧
      (∀ g h (m : thetaSub ψ S T), ((ω (g, h) m : thetaSub ψ S T) : WO S T → ℂ) = om (ιS g, ιT h) m) ∧
      (∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T P m) ∧
      (∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (κ x) m) ∧ (∀ x, IsHalf e (κ x)) ∧
      ∀ u, IsHalf e u → ∃ x, κ x = u := by
  obtain ⟨ϖ, σ, q, π, hU, h2, h, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS⟩ := hV S
  obtain ⟨βT, ιT, hT, gT⟩ := hV T
  obtain ⟨c, hc⟩ := exists_isGen D P
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU h2 (th ψ h c) (th_conj h hU.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ h hU.2.1 hβ ⟨0, ?_⟩ hc
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D P) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap h βS βT c x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (h.half_fin (kap_half h x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap h βS βT c x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D P)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D P)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g k (m : thetaSub ψ S T), (ω (g, k) m : WO S T → ℂ) = om (ιS g, ιT k) m := fun _ _ _ => rfl
  have hlat := kap_mem_iff h hU.2.1 hS hT hc
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half h x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T P m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e e he).2.2.2.1 e' f' he'
    rwa [h.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V P ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D P)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D P)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D P)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  refine ⟨ϖ, σ, q, δ, 1, 1, ψ', ρ, ω, ιS, ιT, kap h βS βT c,
    ⟨hU, odd_of_v_two hU h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_, fun g k x => ?_,
      fun g k hg hk s hs => ?_⟩, hhyp gS, hω, hvac, hρ, kap_half h, fun u hu => kap_surj h hc.1 hu⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap h hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ, kap_add,
      locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · refine span_vacua hψ h.1.1 h.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      refine ⟨kap h βS βT c ((2⁻¹ : LP D P) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
      · rw [map_inv₀, h2, inv_one]
      · rw [← kap_add, half_add_half]
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    show om (ιS g, ιT k) (heisO ψ S T (kap h βS βT c x) m) = heisO ψ S T (kap h βS βT c _) (om (ιS g, ιT k) m)
    rw [hW.om_heis _ _ _ _ m.2, actO_kap h gS gT]
  · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS g).2 hg) _ ((hhyp gT k).2 hk))

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} {e : AE D}

def CommAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (A : Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f) ∧ ∀ u, IsHalf e u → A (heisO ψ S T u f) = heisO ψ S T u (A f)

theorem gen_killed (hH : HoweUnram) (hW : IsWeilDatumO ψ S T χS χT om) (hP : Formalism.DivisionValues.conjPl P = P) (hfix : VacFix ψ om P)
    (he : IsPrimeIdem P e e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hK : ∀ k ∈ hyp S P, om (k, 1) f = f) :
    f ∈ Submodule.span ℂ {φ | ∃ g s, IsVacAt ψ S T P s ∧ (∀ A, CommAt ψ S T e A → A f = 0 → A s = 0) ∧ φ = om (1, g) s} := by
  have : CharZero (LP D P) := algebraRat.charZero _
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', ρ, ω, ιS, ιT, κ, hp, hhyp, hω, hvac, hρ, hκ, -⟩ := exists_pair ψ S T χS χT om P hW hP hfix e he
  have h := howe_killed hH hp {B | ∃ A, CommAt ψ S T e A ∧ A f = 0 ∧ ∀ m, (B m : WO S T → ℂ) = A m}
    (by
      rintro B ⟨A, hA, -, hB⟩ x s
      refine Subtype.ext ?_
      rw [hB, hρ, hρ, hB, (hA _ s.2).2 _ (hκ x)])
    ⟨f, hf⟩ (by rintro B ⟨A, -, hA, hB⟩; exact Subtype.ext ((hB _).trans hA))
    fun g hg => Subtype.ext (by rw [hω, map_one]; exact hK _ ((hhyp g).2 hg))
  have h' := Submodule.mem_map_of_mem (f := (thetaSub ψ S T).subtype) h
  rw [Submodule.map_span] at h'
  refine Submodule.span_mono ?_ h'
  rintro _ ⟨_, ⟨g, s, hs, hA, rfl⟩, rfl⟩
  refine ⟨ιT g, s, (hvac s).1 hs, fun A h1 h2 => ?_, ?_⟩
  · exact congrArg Subtype.val (hA (A.restrict fun _ hm => (h1 _ hm).1) ⟨A, h1, h2, fun _ => rfl⟩)
  · rw [Submodule.subtype_apply, hω, map_one]

theorem rel_transfer_at (hW : IsWeilDatumO ψ S T χS χT om) (hP : Formalism.DivisionValues.conjPl P = P) (hfix : VacFix ψ om P)
    (he : IsPrimeIdem P e e) {ι : Type} [Fintype ι] (u : ι → WO S T) (hu : ∀ k, IsHalf e (u k)) (t t' : ι → WO S T → ℂ)
    (ht : ∀ k, IsVacAt ψ S T P (t k)) (ht' : ∀ k, IsVacAt ψ S T P (t' k))
    (hr : ∀ a : ι → ℂ, ∑ k, a k • t k = 0 → ∑ k, a k • t' k = 0) (h0 : ∑ k, heisO ψ S T (u k) (t k) = 0) :
    ∑ k, heisO ψ S T (u k) (t' k) = 0 := by
  have : CharZero (LP D P) := algebraRat.charZero _
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', ρ, ω, ιS, ιT, κ, hp, -, -, hvac, hρ, -, hκ⟩ := exists_pair ψ S T χS χT om P hW hP hfix e he
  choose x hx using fun k => hκ _ (hu k)
  have h := rel_transfer hp x (fun k => ⟨t k, (ht k).1⟩) (fun k => ⟨t' k, (ht' k).1⟩) (fun k => (hvac _).2 (ht k))
    (fun k => (hvac _).2 (ht' k)) (fun a ha => Subtype.ext (by
      have := congrArg Subtype.val ha
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this ⊢
      exact hr a this)) (Subtype.ext (by
      simp only [Submodule.coe_sum, hρ, hx]
      exact h0))
  have := congrArg Subtype.val h
  simp only [Submodule.coe_sum, hρ, hx] at this
  exact this

theorem commAt_om (hW : IsWeilDatumO ψ S T χS χT om) {k : GA D S} (hk : SuppF S (1 - e) k) : CommAt ψ S T e (om (k, 1)) := by
  refine fun f hf => ⟨hW.om_pres _ _ hf, fun u hu => ?_⟩
  have h1 := (GlobalTheory.IdemSupport.suppF_iff S _ _).1 ((GlobalTheory.IdemSupport.suppGroup S (1 - e)).inv_mem hk)
  rw [sub_sub_cancel] at h1
  have h2 : actO S T k 1 u = u := by
    rw [actO, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
    conv_lhs => rw [← (isHalf_iff _ _).1 hu, Matrix.smul_mul, ← Matrix.mul_smul, h1, Matrix.mul_smul, Matrix.mul_one]
    exact (isHalf_iff _ _).1 hu
  rw [hW.om_heis _ _ _ _ hf, h2]

theorem commAt_heis (hψ : IsStdChar D ψ (-1)) (hc : cA D e = e) {w : WO S T} (hw : w.map (infPart D) = 0) (h0 : e • w = 0) :
    CommAt ψ S T e (heisL ψ S T w) := by
  refine fun f hf => ⟨GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hw hf, fun u hu => ?_⟩
  have : symplO S T u w = 0 := by
    rw [← (isHalf_iff _ _).1 hu, symplO_smul, hc, h0, symplO_zero_right]
  rw [heisL_apply, heisL_apply, heisO_comm ψ S T u w, this, AddChar.map_zero_eq_one, one_smul]

def commSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) : Submodule ℂ (Module.End ℂ (WO S T → ℂ)) where
  carrier := {A | CommAt ψ S T e A}
  add_mem' := fun {A B} hA hB f hf => ⟨theta_add (hA f hf).1 (hB f hf).1, fun u hu => by
    rw [LinearMap.add_apply, LinearMap.add_apply, heisO_add', (hA f hf).2 u hu, (hB f hf).2 u hu]⟩
  zero_mem' := fun f hf => ⟨(thetaSub ψ S T).zero_mem, fun u _ => ((heisL ψ S T u).map_zero).symm⟩
  smul_mem' := fun c A hA f hf => ⟨theta_smul c (hA f hf).1, fun u hu => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, heisO_smul, (hA f hf).2 u hu]⟩

theorem commAt_one : CommAt ψ S T e 1 := fun _ hf => ⟨hf, fun _ _ => rfl⟩

theorem CommAt.vac (he : ∀ e' f', IsPrimeIdem P e' f' → e' = e) (hc : cA D e = e) {A : Module.End ℂ (WO S T → ℂ)}
    (hA : CommAt ψ S T e A) {s : WO S T → ℂ} (hs : IsVacAt ψ S T P s) : IsVacAt ψ S T P (A s) := by
  refine ⟨(hA s hs.1).1, fun e' f' h' u hu hh => ?_⟩
  have hh' := hh
  rw [he e' f' h', hc, or_self] at hh'
  rw [← (hA s hs.1).2 u hh', hs.2 e' f' h' u hu hh]

end Global

section Main

open GlobalTheory.SplitScalar GlobalTheory.FinWeilO GlobalTheory.IdemSupport

variable {D : D7}

theorem mem_dropPl {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v w : HeightOneSpectrum (𝓞 D.host.F)} :
    w ∈ dropPl Sb v ↔ w ≠ v ∧ w ∈ Sb := by
  classical
  unfold dropPl
  convert Finset.mem_erase

theorem suppIn_of_drop {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} {V : HSp D}
    {g : GA D V} (h : SuppIn (dropPl Sb v) V g) : SuppIn Sb V g :=
  ⟨h.1, fun w hw => h.2 w fun h' => hw (mem_dropPl.1 h').2⟩

theorem suppF_of_drop {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} {V : HSp D}
    {g : GA D V} (h : SuppIn (dropPl Sb v) V g) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    SuppF V (1 - algebraMap (AF D.host.F) (AE D) ε) g := fun i j => by
  rw [sub_mul, one_mul, h.2 v (fun h' => (mem_dropPl.1 h').1 rfl) ε hε i j, sub_zero]

theorem suppIn_of_suppF {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Sb)
    {V : HSp D} {g : GA D V} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h : SuppF V (algebraMap (AF D.host.F) (AE D) ε) g) : SuppIn Sb V g := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε' hε' i j => ?_⟩
  · show infPart D _ = 0
    rw [← h i j, RingHom.map_mul, (place_comp hΦ hε).1, zero_mul]
  · rw [← h i j, ← mul_assoc, place_orth hΦ hε' hε (fun h' => hw (h' ▸ hv)), zero_mul]

theorem exists_fixed {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hns : ∀ ε, IsPlaceIdem D v ε → ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) :
    ∃ P : Pl D.host.E, P.under (𝓞 D.host.F) = v ∧ Formalism.DivisionValues.conjPl P = P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    (((RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
      (FaithfulSMul.algebraMap_injective _ _)).le.trans bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact v.ne_bot (hQv.symm.trans (Ideal.comap_bot_of_injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (FaithfulSMul.algebraMap_injective _ _)))
  let P : Pl D.host.E := ⟨Q, hQ.isPrime, hQ0⟩
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv
  refine ⟨P, hPv, by_contra fun hne => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hne
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) v
  have h1 := ev_mul (Φ := Φ) e (algebraMap (AF D.host.F) (AE D) ε) P
  rw [hns ε hε e he.1, ev_zero, (delta_of_isIdemAt hΦ he).2.1, (place_comp hΦ hε).2.1 P hPv, one_mul] at h1
  exact zero_ne_one h1

theorem pure_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by simp
  rw [this, pureTensorL, Module.Basis.constr_basis]
  simp [opPow]

set_option maxHeartbeats 1600000 in

theorem step_inert : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ ε, IsPlaceIdem D v ε → ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hFP i t Sb v hv hns hoff f hT hCl hL
  classical
  have hC := hG.core
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨P, rfl, hP⟩ := exists_fixed hns
  obtain ⟨ε, hε, -, hc, hpi⟩ := GlobalTheory.VacFixInert.inert_data hP
  obtain ⟨e, e', he⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨rfl, rfl⟩ := hpi e e' he
  set e := algebraMap (AF D.host.F) (AE D) ε with he_def
  have hee : e * e = e := place_idem hΦ hε
  have hce : cA D e = e := GlobalTheory.IdemSupport.cA_algebraMap ε
  have hgood : Good R t P := fun PP h => by
    refine ⟨fun h' => hoff PP h (by rw [h']; rfl), fun h' => hoff PP h ?_⟩
    have h1 := under_cP PP
    rw [← (isConjPl_iff PP P).1 h'] at h1
    exact congrArg HeightOneSpectrum.asIdeal h1.symm
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have unr := GlobalTheory.FixAllGood.unrPl_chrTh ((GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hgood).2 ((i : ℕ) + 1) (by omega) i.2)
      (GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hgood).1
  have hr : Odd D.R.r := GlobalTheory.VacFixInert.r_odd
  have ht : Odd D.R.t := D.R.t_odd
  have hfx : VacFix R.ψ (R.ωP i t) P :=
    GlobalTheory.VacFixInert.vacFix_of_inert R.ψ (R.ωP i t) P (hFP i t).inert
      (by rw [hV, hWr]; have := ht.pos; omega) (by left; rw [hV]; exact hr.add_odd ht) hP unr.1 unr.2
  have hW := (hFP i t).datum
  obtain ⟨n, hβ⟩ := hC.lev.βV i
  have hlev := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) (1 ^ n) (R.datVt i t) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top) hgood).1
  have hvP : IsVacAt R.ψ _ _ P (R.vP i t) := by
    have h := (GlobalTheory.VacGood.fock_vacua_good R F hC t P hgood).2.2 i 1
    have e1 : R.ptP i t 1 = R.vP i t := pure_one _ _
    rwa [e1] at h
  have hK : ∀ k ∈ hyp (Vc D i) P, R.ωP i t (k, 1) f = f := fun k hk => by
    obtain ⟨-, a, a', ha, sk⟩ := id hk
    rw [(hpi a a' ha).2] at sk
    rw [hT.2 k (hlev k hk).1 (suppIn_of_suppF hv hε sk), (hlev k hk).2, inv_one, one_smul]
  refine Submodule.span_mono ?_ (gen_killed hH hW hP hfx he hT.1 hK)
  rintro _ ⟨g, s, hs, hA, rfl⟩
  refine ⟨g, s, ⟨hs.1, fun κ hκ hsup => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hs.1, fun c hc h0 => ?_⟩, rfl⟩
  · have h := hA (R.ωP i t (κ, 1) - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • 1)
      ((commSub _ _ _ e).sub_mem (commAt_om hW (suppF_of_drop hsup hε)) ((commSub _ _ _ e).smul_mem _ commAt_one))
      (sub_eq_zero.2 (hT.2 κ hκ (suppIn_of_drop hsup)))
    exact sub_eq_zero.1 h
  · have e1 : ∀ φ, avgW R i t PP a tr z κ φ = (∑ g, (mirC R i PP a tr z g *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1)) φ := fun φ => by
      rw [LinearMap.sum_apply]; rfl
    rw [e1]
    refine hA _ ((commSub _ _ _ e).sum_mem fun g _ => ?_) ?_
    · by_cases hg : mirC R i PP a tr z g = 0
      · rw [hg, zero_mul, zero_smul]; exact (commSub _ _ _ e).zero_mem
      · exact (commSub _ _ _ e).smul_mem _
          (commAt_om hW ((suppGroup _ (1 - e)).inv_mem (suppF_of_drop (hsup g hg) hε)))
    · rw [← e1]
      obtain ⟨w, hw, how⟩ := hov
      exact hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
  · have hz : ∀ u : WO (Vc D i) (Wc D i), e • (1 - e) • u = 0 := fun u => by
      rw [smul_smul, mul_sub, mul_one, hee, sub_self, zero_smul]
    have hh : ∀ u : WO (Vc D i) (Wc D i), IsHalf e (e • u) := fun u => by rw [isHalf_iff, smul_smul, hee]
    have hoffu : ∀ u : c.support, OffPl Sb ((1 - e) • (u : WO (Vc D i) (Wc D i))) := fun u => by
      refine ⟨(finSub _ _).smul_mem (1 - e) (hc u u.2).1, fun w hw ε' hε' a b => ?_⟩
      by_cases hwv : w = P.under (𝓞 D.host.F)
      · subst hwv
        rw [placeIdem_unique hε' hε]
        exact congrFun (congrFun (hz u) a) b
      · rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, (hc u u.2).2 w (mem_dropPl.2 ⟨hwv, hw⟩) ε' hε' a b, mul_zero]
    have hcm : ∀ u : c.support, CommAt R.ψ _ _ e (c u • heisL R.ψ _ _ ((1 - e) • (u : WO (Vc D i) (Wc D i)))) := fun u =>
      (commSub _ _ _ e).smul_mem _ (commAt_heis hW.std hce (hoffu u).1 (hz u))
    have hdec : ∀ φ, (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u φ) =
        ∑ u : c.support, heisO R.ψ _ _ (e • (u : WO (Vc D i) (Wc D i)))
          ((c u • heisL R.ψ _ _ ((1 - e) • (u : WO (Vc D i) (Wc D i)))) φ) := fun φ => by
      rw [Finsupp.sum, ← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h1 : symplO _ _ (e • (u : WO (Vc D i) (Wc D i))) ((1 - e) • (u : WO (Vc D i) (Wc D i))) = 0 := by
        rw [symplO_smul, hce, hz, symplO_zero_right]
      rw [LinearMap.smul_apply, heisO_smul, heisL_apply, ← heisO_add_of_orth _ _ _ h1, ← add_smul, add_sub_cancel, one_smul]
    have hpi' : ∀ e' f', IsPrimeIdem P e' f' → e' = e := fun e' f' h => (hpi e' f' h).1
    rw [hdec] at h0 ⊢
    refine rel_transfer_at hW hP hfx he _ (fun u => hh _) _ _ (fun u => (hcm u).vac hpi' hce hvP)
      (fun u => (hcm u).vac hpi' hce hs) (fun a ha => ?_) h0
    have e1 : ∀ φ, ∑ u : c.support, a u • (c u • heisL R.ψ _ _ ((1 - e) • (u : WO (Vc D i) (Wc D i)))) φ =
        (∑ u : c.support, a u • (c u • heisL R.ψ _ _ ((1 - e) • (u : WO (Vc D i) (Wc D i))))) φ := fun φ => by
      rw [LinearMap.sum_apply]; rfl
    let c' : WO (Vc D i) (Wc D i) →₀ ℂ :=
      ∑ u : c.support, Finsupp.single ((1 - e) • (u : WO (Vc D i) (Wc D i))) (a u * c u)
    have e2 : ∀ φ, (c'.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u φ) =
        ∑ u : c.support, a u • (c u • heisL R.ψ _ _ ((1 - e) • (u : WO (Vc D i) (Wc D i)))) φ := fun φ => by
      rw [← Finsupp.linearCombination_apply ℂ, map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finsupp.linearCombination_single, mul_smul]
      rfl
    have hc' : c' ∈ Finsupp.supported ℂ ℂ {u | OffPl Sb u} :=
      Submodule.sum_mem _ fun u _ => Finsupp.single_mem_supported ℂ _ (hoffu u)
    rw [e1]
    refine hA _ ((commSub _ _ _ e).sum_mem fun u _ => (commSub _ _ _ e).smul_mem _ (hcm u)) ?_
    rw [← e1, ← e2]
    exact hL.2 c' (fun u hu => hc' hu) ((e2 _).trans ha)

end Main

end GlobalTheory.DownLift.GenFinite.Inert

end
