import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSpan

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal TopologicalSpace

theorem exists_pow_smul_of_mem_span {R R' M M' I : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (f : R)
    (hf : ∀ d : R', ∃ (m : ℕ) (d₀ : R), σ d₀ = σ (f ^ m) * d) (t : I → M) (y : M')
    (hy : y ∈ Submodule.span R' (Set.range fun i => φ (t i))) :
    ∃ (n : ℕ) (u : M), u ∈ Submodule.span R (Set.range t) ∧ φ u = σ (f ^ n) • y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨0, t i, Submodule.subset_span ⟨i, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, v, hv, e'⟩ := hz
    refine ⟨n + k, f ^ k • u + f ^ n • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [map_add, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, e', smul_add, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm k n]
  | smul d y _ hy =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, d₀, hd⟩ := hf d
    refine ⟨k + n, d₀ • u, Submodule.smul_mem _ _ hu, ?_⟩
    rw [LinearMap.map_smulₛₗ, e, hd, smul_smul, smul_smul, pow_add, map_mul]
    congr 1
    ring

variable {S : Scheme.{0}} (P : PolAV S)

theorem span_eq_top_of_geomFibres (hS : SecBaseChangeAnySt) [IsAffine S] (N : ℕ) (hN : 1 ≤ N) {I : Type}
    (t : I → SecM P.A P.L N (baseOver S))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ baseOver S),
      Submodule.span Γ((Over.mk w).left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i)) = ⊤) :
    Submodule.span Γ((baseOver S).left, ⊤) (Set.range t) = ⊤ := by
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  refine eq_top_iff.2 fun x _ => ?_
  let J : Ideal Γ((baseOver S).left, ⊤) := (Submodule.span Γ((baseOver S).left, ⊤) (Set.range t)).comap
    (LinearMap.toSpanSingleton _ _ x)
  have key : ∀ p : (baseOver S).left, ∃ f ∈ J, p ∈ (baseOver S).left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top (baseOver S).left).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
    let W := (baseOver S).left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk ((baseOver S).left.homOfLE hf) (by
      change (baseOver S).left.homOfLE hf ≫ V.ι ≫ _ = W.ι ≫ _
      rw [Scheme.homOfLE_ι_assoc])
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, hc⟩ := exists_basis P N b hb (overRes W) l
    have hspan : Submodule.span Γ((overRes W).left, ⊤)
        (Set.range fun i => pullM P.A P.L N (overResι W) (t i)) = ⊤ := by
      refine span_eq_top_of_functionals c _ fun 𝔪 h𝔪 ℓ hl y => ?_
      obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (overRes W).left 𝔪 h𝔪
      let w : Spec (CommRingCat.of K) ⟶ S := u ≫ (overRes W).hom
      let h : Over.mk w ⟶ overRes W := Over.homMk u rfl
      have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
      obtain ⟨b', hb'⟩ := exists_basis P N b hb (Over.mk w) (h ≫ l)
      refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L N h) c b'
        (fun i => by rw [hc, hb', pullM_comp P.A P.isLB]) _ ?_ ℓ (fun i => (hu _).2 (hl i)) y)
      simp only [pullM_comp P.A P.isLB]
      exact H K w _
    obtain ⟨n, u, hu, e⟩ := exists_pow_smul_of_mem_span (overResι W).left.appTop.hom
      (pullM P.A P.L N (overResι W)) f (exists_pow_mul_extend f) t (pullM P.A P.L N (overResι W) x)
      (hspan.ge trivial)
    obtain ⟨k, hk⟩ := exists_pow_kill_secM P N f (f ^ n • x - u) (by
      rw [map_sub, LinearMap.map_smulₛₗ, e, sub_self])
    refine ⟨f ^ k * f ^ n, ?_, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul] at hk
      change (f ^ k * f ^ n) • x ∈ Submodule.span _ _
      rw [hk]
      exact Submodule.smul_mem _ _ hu
    · rw [Scheme.mem_basicOpen_top] at hp ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hp.pow _)
  have hI : Ideal.span (J : Set Γ((baseOver S).left, ⊤)) = ⊤ :=
    (isAffineOpen_top (baseOver S).left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  have := Submodule.mem_comap.1 hI
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at this

theorem pullS_ne_zero (hS : SecBaseChangeAnySt) {T : Over S} [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (hth : IsGenSec P.A P.L 1 th) {K : Type} [Field K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ T) :
    (SecM.ofSec P.A (pullS P.A 1 h th) : SecM P.A P.L 1 (Over.mk w)) ≠ 0 := by
  intro hz
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (w (default : Spec (CommRingCat.of K)))
  let l : Over.mk w ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι w (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim (α := Spec (CommRingCat.of K)) y default]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P 1 b hb (Over.mk w) l
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨r, hr⟩ := isGenSec_pullS P hS h hth (SecM.toSec P.A (c i₀))
  have hr' : c i₀ = r • SecM.ofSec P.A (pullS P.A 1 h th) := Subtype.ext (funext hr)
  exact c.ne_zero i₀ (hr'.trans ((congrArg (r • ·) hz).trans (smul_zero r)))

theorem span_translates_mulPull_of_isGenSec : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : PolAV (Sp R)) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(Sp R, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsGenSec P.A P.L 1 th → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp R)) P.A).left, (snd (baseOver (Sp R)) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver (Sp R))) (t : I → LB.Sec (LPow P.A P.L N (baseOver (Sp R)))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver (Sp R)).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver (Sp R)))) = ⊤ := by
  intro hL hL2 R _ _ _ P m N hN hm hunit th hth α hα s₁ hs₁ I U t hU ht
  subst hN
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN (Sp R) P m hm).2.2.1
  have haff : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec _))
  refine span_eq_top_of_geomFibres P hL2.secBaseChangeAny (m ^ 2) (Nat.one_le_pow _ _ hm) _ fun K _ _ w h => ?_
  obtain rfl : h = Over.homMk w (Category.comp_id _) :=
    Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w h))
  set h : Over.mk w ⟶ baseOver (Sp R) := Over.homMk w (Category.comp_id _)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns (Sp R) P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred (Sp R) P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow (Sp R) P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver (Sp R)) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    exact pullS_ne_zero P hL2.secBaseChangeAny hth w h
      (ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0)

end GlobalTheory.ThetaSpan
