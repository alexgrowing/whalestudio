import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameOpenNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSubQuotientSplitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.FlagVB

theorem exists_gen_of_summand {A E : Type} [CommRing A] [IsLocalRing A] [AddCommGroup E] [Module A E]
    {M M' Q : Submodule A E} (hMM : M ≤ M') (hM' : M' ≤ Q ⊔ M) (hd : Disjoint Q M) {m m' : ℕ} (hm : m' = m + 1)
    (bM : Module.Basis (Fin m) A M) (bM' : Module.Basis (Fin m') A M') :
    ∃ e ∈ M', M' = M ⊔ Submodule.span A {e} := by
  classical
  set P : Submodule A E := Q ⊓ M' with hP
  have hPM' : P ≤ M' := inf_le_right
  have hsup : P ⊔ M = M' := by
    apply le_antisymm (sup_le hPM' hMM)
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hM' hx)
    have hyM' : y ∈ M' := by
      have := M'.sub_mem hx (hMM hz)
      simpa using this
    exact Submodule.mem_sup.2 ⟨y, ⟨hy, hyM'⟩, z, hz, rfl⟩
  have hdP : Disjoint P M := hd.mono_left inf_le_left
  let f : (P × M) →ₗ[A] M' := LinearMap.coprod (Submodule.inclusion hPM') (Submodule.inclusion hMM)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' : (x : E) + (y : E) = 0 := by
      have := congrArg Subtype.val h
      simpa [f] using this
    have hx : (x : E) = -(y : E) := eq_neg_of_add_eq_zero_left h'
    have hxM : (x : E) ∈ M := hx ▸ M.neg_mem y.2
    have hx0 : (x : E) = 0 := (Submodule.disjoint_def.1 hdP) _ x.2 hxM
    have hy0 : (y : E) = 0 := by simpa [hx0] using h'
    ext <;> simp [hx0, hy0]
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hsup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), by ext; simp [f]⟩
  let g : (P × M) ≃ₗ[A] M' := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  haveI : Module.Free A M' := Module.Free.of_basis bM'
  haveI : Module.Finite A M' := Module.Finite.of_basis bM'
  haveI : Module.Free A M := Module.Free.of_basis bM
  haveI : Module.Finite A M := Module.Finite.of_basis bM
  haveI : Module.Free A (P × M) := Module.Free.of_equiv g.symm
  haveI : Module.Finite A (P × M) := Module.Finite.equiv g.symm
  haveI : Module.Finite A P := Module.Finite.of_surjective (LinearMap.fst A P M) LinearMap.fst_surjective
  haveI : Module.Projective A P :=
    Module.Projective.of_split (LinearMap.inl A P M) (LinearMap.fst A P M) (by ext; simp)
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = 1 := by
    have h1 := g.finrank_eq
    rw [Module.finrank_prod, Module.finrank_eq_card_basis bM, Module.finrank_eq_card_basis bM'] at h1
    simp only [Fintype.card_fin] at h1
    omega
  let c : Module.Basis Unit A P := Module.basisUnique Unit hr
  refine ⟨(c ()).1, hPM' (c ()).2, ?_⟩
  have hPs : P = Submodule.span A {((c ()).1 : E)} := by
    have h := c.span_eq
    have h2 := congrArg (Submodule.map P.subtype) h
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h2
    refine h2.symm.trans ?_
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_singleton_iff, Submodule.subtype_apply, exists_exists_eq_and]
    exact ⟨fun ⟨a, h⟩ => h ▸ rfl, fun h => ⟨(), h.symm⟩⟩
  rw [← hPs, sup_comm, hsup]

theorem exists_basis_of_frame {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω) {m : ℕ}
    {b : Fin m → E} (hb : LinearIndependent Ω b) {M : Submodule A E} (hM : M = Submodule.span A (Set.range b)) :
    Nonempty (Module.Basis (Fin m) A M) := by
  subst hM
  have h : LinearIndependent A b := hb.restrict_scalars (by
    intro x y h
    have := congrArg (fun t : Ω => t) h
    simpa [Subring.smul_def] using this)
  exact ⟨Module.Basis.span h |>.map (LinearEquiv.refl _ _)⟩

section Flag

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem flagStep_mono (b : Fin r → E) {i j : ℕ} (h : i ≤ j) : flagStep Ω b i ≤ flagStep Ω b j :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem flagStep_min (b : Fin r → E) (i : ℕ) : flagStep Ω b i = flagStep Ω b (min i r) := by
  unfold flagStep
  congr 2
  ext k
  simp [k.2]

theorem flagStep_last (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem finrank_flagStep {b : Fin r → E} (hb : LinearIndependent Ω b) {n : ℕ} (hn : n ≤ r) :
    Module.finrank Ω (flagStep Ω b n) = n := by
  have h : flagStep Ω b n = Submodule.span Ω (Set.range (b ∘ Fin.castLE hn)) := by
    unfold flagStep
    congr 1
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Fin.castLE hn k, k.2, rfl⟩
  rw [h, finrank_span_eq_card (hb.comp _ (Fin.castLE_injective hn))]
  simp

theorem exists_adapted (A : Subring Ω) [IsLocalRing A] (N : Submodule A E) (b₀ : Fin r → E)
    (hfr : ∀ n ≤ r, ∃ m, m = n ∧ ∃ d : Fin m → E, LinearIndependent Ω d ∧
      Submodule.span Ω (Set.range d) = flagStep Ω b₀ n ∧
      N ⊓ (flagStep Ω b₀ n).restrictScalars A = Submodule.span A (Set.range d))
    (hQ : ∀ n, ∃ Q : Submodule A E, Disjoint Q (N ⊓ (flagStep Ω b₀ n).restrictScalars A) ∧
      Q ⊔ (N ⊓ (flagStep Ω b₀ n).restrictScalars A) = N) :
    ∃ c : ℕ → E, (∀ i ≤ r, Submodule.span Ω (c '' Set.Iio i) = flagStep Ω b₀ i) ∧
      N ⊓ (flagStep Ω b₀ r).restrictScalars A = Submodule.span A (c '' Set.Iio r) := by
  classical
  have key : ∀ n, n ≤ r → ∃ c : ℕ → E, (∀ i ≤ n, Submodule.span Ω (c '' Set.Iio i) = flagStep Ω b₀ i) ∧
      N ⊓ (flagStep Ω b₀ n).restrictScalars A = Submodule.span A (c '' Set.Iio n) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : flagStep Ω b₀ 0 = ⊥ := by simp [flagStep]
      refine ⟨fun _ => 0, fun i hi => ?_, ?_⟩
      · obtain rfl : i = 0 := by omega
        simp [h0]
      · simp [h0]
    | succ n ih =>
      intro hn
      obtain ⟨c, h1, h2⟩ := ih (by omega)
      obtain ⟨m, hm, d, hd, -, hdA⟩ := hfr n (by omega)
      obtain ⟨m', hm', d', hd', hdΩ', hdA'⟩ := hfr (n + 1) hn
      obtain ⟨Q, hQ1, hQ2⟩ := hQ n
      obtain ⟨bM⟩ := exists_basis_of_frame A hd hdA
      obtain ⟨bM'⟩ := exists_basis_of_frame A hd' hdA'
      have hle : flagStep Ω b₀ n ≤ flagStep Ω b₀ (n + 1) := flagStep_mono b₀ (Nat.le_succ n)
      have hMM : N ⊓ (flagStep Ω b₀ n).restrictScalars A ≤ N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A :=
        inf_le_inf_left _ (fun x hx => hle hx)
      have hM' : N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A ≤
          Q ⊔ (N ⊓ (flagStep Ω b₀ n).restrictScalars A) := by
        rw [hQ2]
        exact inf_le_left
      obtain ⟨e, he, hgen⟩ := exists_gen_of_summand hMM hM' hQ1 (by omega) bM bM'
      have himg : ∀ i ≤ n, Function.update c n e '' Set.Iio i = c '' Set.Iio i := fun i hi =>
        Set.image_congr fun k hk => Function.update_of_ne (by
          have : k < i := hk
          omega) _ _
      have himg' : Function.update c n e '' Set.Iio (n + 1) = insert e (c '' Set.Iio n) := by
        have : Set.Iio (n + 1) = insert n (Set.Iio n) := by
          ext k
          simp only [Set.mem_Iio, Set.mem_insert_iff]
          omega
        rw [this, Set.image_insert_eq, Function.update_self, himg n le_rfl]
      refine ⟨Function.update c n e, fun i hi => ?_, ?_⟩
      · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
        · rw [himg i (by omega), h1 i (by omega)]
        · obtain rfl : i = n + 1 := by omega
          rw [himg', Submodule.span_insert, h1 n le_rfl]
          apply le_antisymm
          · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 he.2) hle
          · rw [← hdΩ', Submodule.span_le]
            rintro _ ⟨k, rfl⟩
            have hk : d' k ∈ N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A := by
              rw [hdA']
              exact Submodule.subset_span ⟨k, rfl⟩
            rw [hgen] at hk
            obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hk
            obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
            rw [← hyz]
            refine add_mem (Submodule.mem_sup_right hy.2) (Submodule.mem_sup_left ?_)
            exact Submodule.smul_mem _ (a : Ω) (Submodule.mem_span_singleton_self e)
      · rw [himg', Submodule.span_insert, ← h2, hgen, sup_comm]
  obtain ⟨c, h1, h2⟩ := key r le_rfl
  exact ⟨c, h1, h2⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.FlagVB

namespace GlobalTheory.CompanionTheory.Ar

theorem isFlagVBOn_inter_of_steps : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g r : ℕ) (W : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → (∀ k, b₀ k ∈ W) → L.IsVBOn T g W → (∀ n : ℕ, ∃ s W', (L.map (flagStep Ω b₀ n).mkQ).IsVBOn T s W') → (L.inter (Submodule.span Ω (Set.range b₀))).IsFlagVBOn T b₀ := by
  intro X Ω _ ξ E _ _ L T g r W b₀ hli hW hL hq p hp
  classical
  haveI : IsLocalRing (regAt ξ p) := (GlobalTheory.T.regAt_local_order_fraction X Ω ξ).1 p
  have hFW : ∀ n, flagStep Ω b₀ n ≤ W := fun n =>
    Submodule.span_le.2 (by
      rintro _ ⟨k, -, rfl⟩
      exact hW k)
  have hv : ∀ n, (L.inter (flagStep Ω b₀ n)).IsVBOn T (Module.finrank Ω (flagStep Ω b₀ n)) (flagStep Ω b₀ n) ∧
      ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter (flagStep Ω b₀ n) p) ∧
        Q ⊔ L.inter (flagStep Ω b₀ n) p = L p := fun n => by
    obtain ⟨s, W', h⟩ := hq n
    exact GlobalTheory.T.lattice_sub_quotient_split X Ω ξ E L T g s W (flagStep Ω b₀ n) W' (hFW n) hL h
  obtain ⟨c, h1, h2⟩ := FlagVB.exists_adapted (regAt ξ p) (L p) b₀ (fun n hn => by
      obtain ⟨U, hU, d, hd, hfr⟩ := (hv n).1 p hp
      obtain ⟨hd1, hd2⟩ := hfr p hp hU
      exact ⟨_, FlagVB.finrank_flagStep hli hn, d, hd1, hd, hd2⟩)
    (fun n => (hv n).2 p hp)
  let b : Fin r → E := fun k => c k
  have himg : ∀ i, b '' {k | (k : ℕ) < i} = c '' Set.Iio (min i r) := fun i => by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, lt_min hk k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' := lt_min_iff.1 (show k < min i r from hk)
      exact ⟨⟨k, hk'.2⟩, hk'.1, rfl⟩
  have hflag : ∀ i, flagStep Ω b i = flagStep Ω b₀ i := fun i => by
    rw [FlagVB.flagStep_min b₀ i, ← h1 (min i r) (min_le_right _ _), ← himg i]
    rfl
  have hrange : Set.range b = c '' Set.Iio r := by
    have := himg r
    rw [min_self] at this
    rw [← this]
    ext x
    simp
  have hspan : Submodule.span Ω (Set.range b) = flagStep Ω b₀ r := by
    rw [hrange, h1 r le_rfl]
  have hlib : LinearIndependent Ω b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, FlagVB.finrank_flagStep hli le_rfl]
    simp
  have hV : Submodule.span Ω (Set.range b₀) = flagStep Ω b₀ r := (FlagVB.flagStep_last b₀).symm
  have hframe : (L.inter (Submodule.span Ω (Set.range b₀))).IsFrameAt b p := by
    refine ⟨hlib, ?_⟩
    rw [hV, hrange]
    exact h2
  have hcoh : (L.inter (Submodule.span Ω (Set.range b₀))).IsCohOn T := by
    have hvb := (hv r).1
    rw [← hV] at hvb
    exact (GlobalTheory.T.coherent_lattice_closure X Ω ξ E E (L.inter (Submodule.span Ω (Set.range b₀))) (L.inter (Submodule.span Ω (Set.range b₀))) T).1 _ _ hvb
  obtain ⟨U, hU, hall⟩ := GlobalTheory.T.frame_open_neighbourhood X Ω ξ E _ T r b p hcoh hp hframe
  exact ⟨U, hU, b, hflag, hall⟩

end GlobalTheory.CompanionTheory.Ar
