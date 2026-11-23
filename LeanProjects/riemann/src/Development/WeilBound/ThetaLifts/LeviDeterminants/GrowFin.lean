import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible

noncomputable section

namespace PositivityTheory.ThKF0.Grow.Fi

open scoped Matrix NNReal ENNReal Classical Pointwise
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Int' (a : Af F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F

theorem Int'.nsmul {a : Af F} (h : Int' a) (k : ℕ) : Int' (k • a) := fun v => by
  have : (k • a) v = k • a v := map_nsmul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k a
  rw [this]
  exact nsmul_mem (h v) k

theorem exists_pi (U : Set (κ → Af F)) (hU : U ∈ 𝓝 (0 : κ → Af F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ M, N ∣ M → ∀ a : κ → Af F, (∀ i, Int' (a i)) → M • a ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose N hN h using fun i => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (t i) (ht i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun M hM a ha => hI fun i _ => ?_⟩
  obtain ⟨k, rfl⟩ := (Finset.dvd_prod_of_mem N (Finset.mem_univ i)).trans hM
  rw [Pi.smul_apply, mul_smul]
  exact h i _ ((ha i).nsmul k)

theorem eventually_fix (c : Af F → ℂ) (hc : IsLocallyConstant c) (h0 : c 0 = 1) (e : Af F) {g : (κ → Af F) → ℂ}
    (hg : g ∈ SB (κ → Af F)) : ∀ᶠ w in 𝓝 (0 : (κ → Af F) × (κ → Af F)), ∀ x,
      c (x ⬝ᵥ w.2 + e * (w.1 ⬝ᵥ w.2)) * g (x + w.1) = g x := by
  let C : Set (κ → Af F) := Set.pi Set.univ fun _ => {a | Int' a}
  have hC : IsCompact C := isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F
  have hO : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.AdLat.OpenLat.isOpen_integral F
  have hz : (0 : κ → Af F) ∈ C := fun i _ v => zero_mem _
  have hK : IsCompact ((fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C)) :=
    (hg.2.isCompact.prod hC).image (by fun_prop)
  have h1 : ∀ᶠ w in 𝓝 (0 : (κ → Af F) × (κ → Af F)),
      ∀ x ∈ (fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C),
      c (x ⬝ᵥ w.2 + e * (w.1 ⬝ᵥ w.2)) * g (x + w.1) = g x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have l1 : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) =>
        c (z.2 ⬝ᵥ z.1.2 + e * (z.1.1 ⬝ᵥ z.1.2)) * g (z.2 + z.1.1) :=
      (hc.comp_continuous (by unfold dotProduct; fun_prop)).mul (hg.1.comp_continuous (by fun_prop))
    have l2 : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) => g z.2 :=
      hg.1.comp_continuous continuous_snd
    filter_upwards [l1.eventually_eq (0, x), l2.eventually_eq (0, x)] with z e1 e2
    rw [e1, e2]
    simp [h0]
  filter_upwards [h1, (hO.preimage continuous_fst).mem_nhds (show (0 : (κ → Af F) × (κ → Af F)) ∈ _ from hz)]
    with w hw hw' x
  by_cases hx : x ∈ (fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C)
  · exact hw x hx
  · have a1 : g (x + w.1) = 0 := by
      by_contra hne
      exact hx ⟨(x + w.1, w.1), ⟨subset_tsupport _ hne, hw'⟩, by simp⟩
    have a2 : g x = 0 := by
      by_contra hne
      exact hx ⟨(x, 0), ⟨subset_tsupport _ hne, hz⟩, by simp⟩
    rw [a1, a2, mul_zero]

theorem intF_nat {a : AF F} (h : IntF a) (k : ℕ) : IntF ((k : AF F) * a) := by
  refine ⟨?_, fun v => ?_⟩
  · change (k : AF F).1 * a.1 = 0
    rw [h.1, mul_zero]
  · rw [map_mul, map_natCast]
    exact mul_mem (natCast_mem _ k) (h.2 v)

theorem integralPoint_natCast_smul {w : Pt F κ} (h : IntP w) (k : ℕ) : IntP ((k : AF F) • w) :=
  ⟨fun i => intF_nat (h.1 i) k, fun i => intF_nat (h.2 i) k⟩

theorem dot_fst (x y : κ → AF F) (hy : ∀ i, (y i).1 = 0) : (x ⬝ᵥ y).1 = 0 :=
  (map_sum (RingHom.fst (Ainf F) (Af F)) _ Finset.univ).trans (Finset.sum_eq_zero fun i _ => by
    change (x i).1 * (y i).1 = 0
    rw [hy i, mul_zero])

theorem dot_snd (x y : κ → AF F) : (x ⬝ᵥ y).2 = (fun i => (x i).2) ⬝ᵥ fun i => (y i).2 :=
  map_sum (RingHom.snd (Ainf F) (Af F)) _ Finset.univ

theorem fix_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Pt F κ, IntP w → schr ψ ((m : AF F) • w) (pureA F f g) = pureA F f g := by
  let ψf : AddChar (Af F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))
  have hl : IsLocallyConstant ψf := GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin ψf
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _
  obtain ⟨U, hU, U', hU', h⟩ := mem_nhds_prod_iff.1 (eventually_fix ψf hl ψf.map_zero_eq_one (⅟(2 : AF F)).2 hg)
  obtain ⟨N, hN, h1⟩ := exists_pi U hU
  obtain ⟨N', hN', h2⟩ := exists_pi U' hU'
  refine ⟨N * N', Nat.mul_pos hN hN', fun w hw => funext fun x => ?_⟩
  have hw' := integralPoint_natCast_smul hw (N * N')
  have e1 : (fun i => ((((N * N' : ℕ) : AF F) • w).1 i).2) = (N * N') • fun i => (w.1 i).2 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul]; rfl
  have e2 : (fun i => ((((N * N' : ℕ) : AF F) • w).2 i).2) = (N * N') • fun i => (w.2 i).2 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul]; rfl
  have key := h (Set.mk_mem_prod (h1 _ (dvd_mul_right N N') (fun i => (w.1 i).2) fun i => (hw.1 i).2)
    (h2 _ (dvd_mul_left N' N) (fun i => (w.2 i).2) fun i => (hw.2 i).2)) fun i => (x i).2
  rw [← e1, ← e2] at key
  generalize ((N * N' : ℕ) : AF F) • w = u at hw' key
  have p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψf (((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) +
      (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) := by
    rw [← dot_snd, ← dot_snd]
    refine congrArg ψ (Prod.ext ?_ rfl)
    change (x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0
    rw [dot_fst _ _ fun i => (hw'.2 i).1, dot_fst _ _ fun i => (hw'.2 i).1, mul_zero, add_zero]
  have q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _
    rw [(hw'.1 i).1, add_zero]
  simp only [schr, pureA]
  rw [p, q, mul_left_comm]
  exact congrArg _ key

theorem fix {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Pt F κ, IntP w → schr ψ ((m : AF F) • w) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact fix_pure hψ f hg
  | zero => exact ⟨1, le_rfl, fun w _ => funext fun x => by simp [schr]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, h⟩ := ha
    obtain ⟨m', hm', h'⟩ := hb
    refine ⟨m * m', Nat.mul_pos hm hm', fun w hw => funext fun x => ?_⟩
    have e1 := congrFun (h _ (integralPoint_natCast_smul hw m')) x
    have e2 := congrFun (h' _ (integralPoint_natCast_smul hw m)) x
    rw [smul_smul] at e1 e2
    rw [mul_comm] at e2
    rw [Nat.cast_mul, Pi.add_apply, ← e1, ← e2]
    simp only [schr, Pi.add_apply, mul_add]
  | smul c a _ ha =>
    obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, fun w hw => funext fun x => ?_⟩
    rw [Pi.smul_apply, ← congrFun (h w hw) x]
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    ring

end PositivityTheory.ThKF0.Grow.Fi

namespace PositivityTheory.ThKF0.Grow

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem finInv : FinInv := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m, hm, h⟩ := Fi.fix hψ hΦ
  refine ⟨m, hm, fun T s d c hT hs w hw => ?_⟩
  rw [← hT.impl _ Φ hΦ, map_smul, Nat.cast_mul, mul_smul, h _ (hs.fin w hw)]

end PositivityTheory.ThKF0.Grow
