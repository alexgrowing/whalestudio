import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlChBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_surj {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom R p) := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single g c =>
    obtain ⟨g', rfl⟩ := hp g
    exact ⟨MonoidAlgebra.single g' c, by simp⟩

private theorem md_ker {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z = 0) : z ∈ J := by
  choose s hs using hp
  have key : ∀ z : MonoidAlgebra R G,
      z - MonoidAlgebra.mapDomain s (MonoidAlgebra.mapDomainRingHom R p z) ∈ J := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g c =>
      have h := J.mul_mem_left (MonoidAlgebra.single (s (p g)) c) _ (hJ ((s (p g))⁻¹ * g) (by simp [hs]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_inv_cancel_left] at h
      simpa using h
  have := key z
  rw [hz] at this
  simpa using this

private theorem md_span {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (S : Set (MonoidAlgebra R G')) (hS : ∀ y ∈ S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ TwoSidedIdeal.span S) : z ∈ J := by
  have key : ∀ y ∈ TwoSidedIdeal.span S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y := by
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy => exact hS y hy
    | zero => exact ⟨0, J.zero_mem, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨b', h2, rfl⟩ := hb
      exact ⟨a' + b', J.add_mem h1 h2, map_add _ _ _⟩
    | neg a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      exact ⟨-a', J.neg_mem h1, map_neg _ _⟩
    | left_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨c' * a', J.mul_mem_left _ _ h1, map_mul _ _ _⟩
    | right_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨a' * c', J.mul_mem_right _ _ h1, map_mul _ _ _⟩
  obtain ⟨x, hx, e⟩ := key _ hz
  have := J.add_mem (md_ker p hp J hJ (z - x) (by rw [map_sub, e, sub_self])) hx
  rwa [sub_add_cancel] at this

private theorem nonSS_down {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ I)
    (hI : ∀ z, MonoidAlgebra.mapDomainRingHom R p z ∈ I' → z ∈ I) (Q : Ideal R) :
    NonSS I (RingHom.id R) Q → NonSS I' (RingHom.id R) Q := by
  rintro ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  rw [RingHom.comp_id] at hs ⊢
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' f '' I') with hJ'
  have hcomm : ∀ w : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G f w) =
        MonoidAlgebra.mapRingHom G' f (MonoidAlgebra.mapDomainRingHom R p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g c => simp
  have hkJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J := fun k h =>
    TwoSidedIdeal.subset_span ⟨_, hk k h, by rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one]⟩
  have hpre : ∀ z, MonoidAlgebra.mapDomainRingHom κ p z ∈ J' → z ∈ J := by
    refine md_span p hp J hkJ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := md_surj (R := R) p hp y
    exact ⟨_, TwoSidedIdeal.subset_span ⟨x, hI x hy, rfl⟩, hcomm x⟩
  have hs' := md_surj (R := κ) p hp
  have hle : RingHom.ker (MonoidAlgebra.mapDomainRingHom κ p) ≤ RingHom.ker J.ringCon.mk' := by
    intro z hz
    rw [RingHom.mem_ker] at hz ⊢
    have h1 : z - 0 ∈ J := by rw [sub_zero]; exact md_ker p hp J hkJ z hz
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h1)
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    (MonoidAlgebra.mapDomainRingHom κ p).liftOfSurjective hs' ⟨J.ringCon.mk', hle⟩
  have hψ : ∀ x, ψ (MonoidAlgebra.mapDomainRingHom κ p x) = J.ringCon.mk' x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    obtain ⟨a, rfl⟩ := hs' a
    obtain ⟨b, rfl⟩ := hs' b
    have h1 := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    rw [← map_sub] at h1
    rw [hψ, hψ]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (hpre _ h1))
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := RingCon.mk'_surjective _ y
  exact ⟨((MonoidAlgebra.mapDomainRingHom κ p x : MonoidAlgebra κ G') : J'.ringCon.Quotient), hψ x⟩

private theorem closure_down {R G G' : Type} [CommRing R] [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    (p : G →* G') (hp : Function.Surjective p) (ho : IsOpenMap p) (m : Ideal R)
    (S : Set (MonoidAlgebra R G)) (S' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ closureIdeal m S)
    (hS : ∀ y ∈ S', ∃ x ∈ S, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ closureIdeal m S') : z ∈ closureIdeal m S := by
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hk hz ⊢
  intro N V
  let V' : OpenNormalSubgroup G' :=
    { toSubgroup := V.toSubgroup.map p
      isOpen' := ho _ V.isOpen'
      isNormal' := V.isNormal'.map p hp }
  refine md_span p hp _ (fun k h => hk k h N V) _ ?_ z (hz N V')
  rintro y ((hy | ⟨a, ha, rfl⟩) | ⟨_, ⟨h, hh, rfl⟩, rfl⟩)
  · obtain ⟨x, hx, e⟩ := hS y hy
    exact ⟨x, TwoSidedIdeal.subset_span (Or.inl (Or.inl hx)), e⟩
  · exact ⟨MonoidAlgebra.single 1 a, TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩)), by simp⟩
  · exact ⟨MonoidAlgebra.single h 1 - 1, TwoSidedIdeal.subset_span (Or.inr ⟨h, hh, rfl⟩), by
      rw [map_sub, map_one]; simp⟩

theorem UpperTheory.V.Pa.nonss_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → u'.D.comap g.p₀ = u.D → u'.ψ = u.ψ → ∀ q : Ideal B, (NonSS (augmentationIdealKernel u) (RingHom.id B) q → NonSS (augmentationIdealKernel u') (RingHom.id B) q) ∧ (DiscSt u.D q ↔ DiscSt u'.D q) := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u u' H _ hHo hHle hHchi hker hcomp hD hψ q
  refine ⟨?_, ?_⟩
  · have hk : ∀ k : G.G₀, g.p₀ k = 1 → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar (pairGens u) := fun k h =>
      pl_chBar l L G n O r B u H hHo hHle hHchi _ k (by
        rw [← hker, MonoidHom.mem_ker]; exact congrArg Subtype.val h)
    have ho : IsOpenMap g.p₀ := (MonoidHom.isOpenQuotientMap_of_isQuotientMap g.p₀_quot).isOpenMap
    obtain ⟨hst, hoel, -⟩ := map_star l L G G' g n O B
    have hCH := ((comap_lam n B _ _ g.p₀ u'.D).2.2.2.2.2 g.p₀_surj).2
    rw [hD] at hCH
    refine nonSS_down g.p₀ g.p₀_surj _ _ hk (fun z hz => ?_) q
    refine closure_down g.p₀ g.p₀_surj ho _ _ _ hk ?_ z hz
    rintro y (hy | ⟨v, a, h⟩ | ⟨w, _, ⟨⟨a, ha, rfl⟩, hb⟩, h⟩)
    · rw [← hCH] at hy
      obtain ⟨x, hx, e⟩ := hy
      exact ⟨x, Or.inl hx, e⟩
    · rw [hψ] at h
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inl rfl⟩), hoel v _ a⟩
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inr rfl⟩), by rw [hst]; exact congrArg _ (hoel v _ a)⟩
    · have hm : G.φu w a ∈ r.Ip w := by
        refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
        have hb' : r'.chib i (G'.φu w a) = 1 := Subgroup.mem_iInf.1 hb i
        have e1 : r.chib i (G.φu w a) = r'.chib i (g.p₀ (G.φu w a)) := DFunLike.congr_fun (hcomp.1 i) _
        rw [g.p₀_φu] at e1
        exact e1.trans hb'
      have e : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.single (G.φu w a) 1) =
          MonoidAlgebra.single (G'.φu w a) 1 := by
        rw [← g.p₀_φu]; simp
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inl rfl⟩), by rw [map_sub, map_one, e]⟩
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inr rfl⟩), by rw [map_sub, map_one, hst, e]⟩
  · rw [← hD]
    exact (BC.discSt_map n B B _ u'.D).2.1 _ g.p₀ g.p₀_surj q
