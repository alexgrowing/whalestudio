import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ImHermFormEqCurveForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.GBack

variable {K : Type} [Field K] [NumberField K]

theorem exists_prodFam (B : Out.PolAV (Sp (𝓞 K))) : ∀ (n : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))),
    ∃ (Q : Out.PolAV (Sp (𝓞 K))) (a : ∀ k, Q.A ⟶ (C k).A), (∀ k, IsMonHom (a k)) ∧ Q.g = ∑ k, (C k).g ∧
      (∀ (T : Over (Sp (𝓞 K))) (x : ∀ k, T ⟶ (C k).A), ∃ z : T ⟶ Q.A, ∀ k, z ≫ a k = x k) ∧
      ∀ (T : Over (Sp (𝓞 K))) (z z' : T ⟶ Q.A), (∀ k, z ≫ a k = z' ≫ a k) → z = z' := by
  intro n
  induction n with
  | zero =>
    intro C
    obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) B 0
    refine ⟨P, fun k => Fin.elim0 k, fun k => Fin.elim0 k, by simp [hP], fun T x => ?_, fun T z z' _ => ?_⟩
    · exact ⟨pP.lim.lift (Fan.mk T fun i => Fin.elim0 i), fun k => Fin.elim0 k⟩
    · exact pP.lim.hom_ext fun j => Fin.elim0 j.as
  | succ n ih =>
    intro C
    obtain ⟨Q', a', ha', hg', hex', hext'⟩ := ih fun k => C k.succ
    obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g GlobalTheory.CMClaims.laws (𝓞 K) (C 0) Q'
    refine ⟨Q, Fin.cases u fun j => v ≫ a' j, fun k => ?_, ?_, fun T x => ?_, fun T z z' h => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact hu
      · haveI := hv; haveI := ha' j; show IsMonHom (v ≫ a' j); infer_instance
    · rw [hQ, hg', Fin.sum_univ_succ]
    · obtain ⟨z', hz'⟩ := hex' T fun j => x j.succ
      have e1 : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
      have e2 : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
      refine ⟨lift (x 0) z' ≫ inv (lift u v), fun k => Fin.cases ?_ (fun j => ?_) k⟩
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ u = x 0
        rw [Category.assoc, e1, lift_fst]
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ v ≫ a' j = x j.succ
        rw [Category.assoc, reassoc_of% e2, lift_snd_assoc, hz']
    · rw [← cancel_mono (lift u v)]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst]
        exact h 0
      · simp only [Category.assoc, lift_snd]
        exact hext' T _ _ fun j => by
          have := h j.succ
          simp only [Fin.cases_succ] at this
          simpa only [Category.assoc] using this

theorem isMonHom_pow {G H : Over (Sp (𝓞 K))} [GrpObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (N : ℕ) :
    IsMonHom (f ^ N) :=
  GlobalTheory.LamF.IsogSum.isMonHom_of_points _ fun T x y => by
    rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_pow, MonObj.mul_comp, mul_pow]

end GlobalTheory.CompanionTheory.Ggeo.GBack

open GlobalTheory.CompanionTheory.Ggeo.GBack in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n N : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))) (B : Out.PolAV (Sp (𝓞 K))) (ψ : ∀ k, (C k).A ⟶ B.A), (∀ k, IsMonHom (ψ k)) → 0 < N → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, y = (List.ofFn fun k => x k ≫ ψ k).prod) → (∀ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, (List.ofFn fun k => x k ≫ ψ k).prod = 1 → ∀ k, x k ^ N = 1) → ∃ χ : ∀ k, B.A ⟶ (C k).A, (∀ k, IsMonHom (χ k)) ∧ (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) ∧ ∀ k k', k ≠ k' → ψ k ≫ χ k' = 1 := by
  intro K _ _ σ n N C B ψ hψ hN hon hker
  have hNo : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  obtain ⟨Q, a, ha, hQg, hex, hext⟩ := exists_prodFam B n C
  have := B.isAb.comm
  have := Q.isAb.comm
  have hCc : ∀ k, IsCommMonObj (C k).A := fun k => (C k).isAb.comm
  let Φ : Q.A ⟶ B.A := ∏ k, a k ≫ ψ k
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A), x ≫ Φ = ∏ k, (x ≫ a k) ≫ ψ k := by
    intro T x
    simp only [Φ, GlobalTheory.LamF.IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := GlobalTheory.LamF.IsogSum.isMonHom_of_points Φ fun T x y => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
  let t : Sp ℂ ⟶ Sp (𝓞 K) := spMap (σ.comp (algebraMap (𝓞 K) K))
  have onto : ∀ y : Over.mk t ⟶ B.A, ∃ z : Over.mk t ⟶ Q.A, y = z ≫ Φ := by
    intro y
    obtain ⟨x, hx⟩ := hon y
    obtain ⟨z, hz⟩ := hex _ x
    refine ⟨z, ?_⟩
    rw [hΦ, hx, List.prod_ofFn]
    simp only [hz]
  have kerN : ∀ z : Over.mk t ⟶ Q.A, z ≫ Φ = 1 → z ^ N = 1 := by
    intro z hz
    have h1 := hker (fun k => z ≫ a k) (by rw [List.prod_ofFn, ← hΦ]; exact hz)
    apply hext
    intro k
    rw [MonObj.pow_comp, h1 k, MonObj.one_comp]
  have hg : Q.g = B.g := by
    let F : (Over.mk t ⟶ Q.A) →* (Over.mk t ⟶ B.A) := MonoidHom.mk' (· ≫ Φ) fun x y => MonObj.mul_comp x y Φ
    obtain ⟨m, hmN⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have e := GlobalTheory.CMClaims.card_torsion_eq F (fun y => (onto y).imp fun _ h => h.symm) m
      (fun x hx => hmN ▸ kerN x hx)
    have h0 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    rw [(GlobalTheory.CMClaims.laws.mulN _ Q (m + 2) (by omega)).2.2.2.2 ℂ t h0,
      (GlobalTheory.CMClaims.laws.mulN _ B (m + 2) (by omega)).2.2.2.2 ℂ t h0] at e
    have := Nat.pow_right_injective (by omega : 2 ≤ m + 2) e
    omega
  obtain ⟨N₀, ψ₀, hN₀, hψ₀, h1, h2⟩ := GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers GlobalTheory.thetaUnifAV_all
    GlobalTheory.CMClaims.laws GlobalTheory.CMClaims.homExt K σ Q B Φ hg hm onto
  have divQ : ∀ q : Over.mk t ⟶ Q.A, ∃ q', q = q' ≫ (𝟙 Q.A ^ N₀) := by
    intro q
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).1
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).2.2.1
    exact GlobalTheory.CMClaims.onto_points (𝟙 Q.A ^ N₀) t q
  have cancel : ∀ (Z : Out.PolAV (Sp (𝓞 K))) (X Y : Q.A ⟶ Z.A), (𝟙 Q.A ^ N₀) ≫ X = (𝟙 Q.A ^ N₀) ≫ Y → X = Y := by
    intro Z X Y h
    have := Q.isAb.smooth
    have := Z.isAb.proper
    refine GlobalTheory.CMPointCompare.hom_ext_of_complexPoints (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) fun q => ?_
    obtain ⟨q', rfl⟩ := divQ q
    rw [Category.assoc, Category.assoc, h]
  have hf : ∀ k, IsMonHom ((ψ₀ ≫ a k) ^ N) := fun k => by
    have := ha k
    exact isMonHom_pow (ψ₀ ≫ a k) N
  have kill : ∀ k (b : Over.mk t ⟶ B.A), b ^ N₀ = 1 → b ≫ (ψ₀ ≫ a k) ^ N = 1 := by
    intro k b hb
    obtain ⟨z, rfl⟩ := onto b
    have e1 : (z ^ N₀) ≫ Φ = 1 := by rw [MonObj.pow_comp, hb]
    have e2 := kerN _ e1
    rw [MonObj.comp_pow]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← Category.assoc, MonObj.comp_pow, Category.comp_id, ← MonObj.pow_comp, e2, MonObj.one_comp]
  choose χ hχ hχe using fun k => GlobalTheory.T.exists_nth_root_homomorphism K σ N₀ B (C k) ((ψ₀ ≫ a k) ^ N) (hf k) hN₀ (kill k)
  have key : ∀ k, Φ ≫ χ k = a k ^ N := by
    intro k
    apply cancel (C k)
    have := hχ k
    rw [← h1, Category.assoc, ← Category.assoc ψ₀, h2, MonObj.pow_comp, Category.id_comp, hχe k, MonObj.comp_pow,
      ← Category.assoc, h1, MonObj.comp_pow]
  refine ⟨χ, hχ, ?_⟩
  have inc : ∀ k, ∃ z : (C k).A ⟶ Q.A, ∀ j, z ≫ a j = if h : k = j then eqToHom (by rw [h]) else 1 :=
    fun k => hex _ fun j => if h : k = j then eqToHom (by rw [h]) else 1
  choose inc hinc using inc
  have hincPhi : ∀ k, inc k ≫ Φ = ψ k := by
    intro k
    rw [hΦ, Finset.prod_eq_single k]
    · rw [hinc, dif_pos rfl, eqToHom_refl, Category.id_comp]
    · intro j _ hj
      rw [hinc, dif_neg (Ne.symm hj), MonObj.one_comp]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hψχ : ∀ k k', ψ k ≫ χ k' = (inc k ≫ a k') ^ N := by
    intro k k'
    rw [← hincPhi, Category.assoc, key, MonObj.comp_pow]
  refine ⟨fun k => ?_, fun k k' hk => ?_⟩
  · rw [hψχ, hinc, dif_pos rfl, eqToHom_refl]
  · rw [hψχ, hinc, dif_neg hk, one_pow]
