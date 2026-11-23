import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg

section Hopf

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) {f : T → R} (hf : f ∈ A) (t : T) :
    (fun x => f (t * x)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun x => g (t, x)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g h =>
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add g g' _ _ h h' => exact A.add_mem h h'
    | smul c g _ h => exact A.smul_mem h c
  exact key _ (hA.comul f hf)

theorem augIdeal_fg {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) : (augIdeal A).FG := by
  classical
  haveI := hA.finite
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  let π : A →ₗ[R] A := LinearMap.id - (Algebra.linearMap R A) ∘ₗ (evalAt A 1).toLinearMap
  have hπ : ∀ a : A, π a = a - algebraMap R A ((a : T → R) 1) := fun a => rfl
  have hJ : ∀ a : A, π a ∈ augIdeal A := by
    intro a
    rw [OrderApi.mem_augIdeal, hπ]
    simp
  refine ⟨s.image π, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro g hg
    obtain ⟨g', _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
    exact hJ g'
  · intro a ha
    have ha' : a ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    have key : ∀ x ∈ Submodule.span R (s : Set A), π x ∈ Ideal.span ((s.image π : Finset A) : Set A) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x h => exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem π (Finset.mem_coe.1 h)))
      | zero => simp
      | add x x' _ _ h h' => rw [map_add]; exact Ideal.add_mem _ h h'
      | smul c x _ h =>
        rw [map_smul, ← algebraMap_smul A c]
        exact Submodule.smul_mem _ _ h
    have h1 : π a = a := by
      rw [hπ, (OrderApi.mem_augIdeal A a).1 ha]
      simp
    rw [← h1]
    exact key a ha'

theorem det_trick {B : Type} [CommRing B] (J : Ideal B) (hfg : J.FG) (c : B) (h : ∀ x ∈ J, c * x ∈ J ^ 2) :
    ∃ (u : B) (k : ℕ), (∀ x ∈ J, u * x = 0) ∧ u - c ^ k ∈ J := by
  haveI : Module.Finite B J := Module.Finite.iff_fg.2 hfg
  let fJ : Module.End B J := algebraMap B (Module.End B J) c
  have hfx : ∀ x : J, fJ x = c • x := fun x => Module.algebraMap_end_apply B B J c x
  have hrange : LinearMap.range fJ ≤ J • (⊤ : Submodule B J) := by
    rintro _ ⟨x, rfl⟩
    have h1 : ((fJ x : J) : B) ∈ Submodule.map J.subtype (J • (⊤ : Submodule B J)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, smul_eq_mul, ← sq, hfx]
      exact h x x.2
    obtain ⟨y, hy, hxy⟩ := h1
    have : y = fJ x := Subtype.ext hxy
    exact this ▸ hy
  obtain ⟨q, hmon, -, hcoef, hq⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul B fJ J hrange
  refine ⟨q.eval c, q.natDegree, fun x hx => ?_, ?_⟩
  · have h2 : Polynomial.aeval fJ q = algebraMap B (Module.End B J) (q.eval c) := by
      change Polynomial.aeval (algebraMap B (Module.End B J) c) q = _
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
    have h3 := LinearMap.congr_fun (h2.symm.trans hq) ⟨x, hx⟩
    have h4 : q.eval c • (⟨x, hx⟩ : J) = 0 := by simpa [Module.algebraMap_end_apply] using h3
    simpa using congrArg Subtype.val h4
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, _root_.one_mul, add_sub_cancel_right]
    refine sum_mem fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : i < q.natDegree := Finset.mem_range.1 hi
    exact Ideal.pow_le_self (by omega) (hcoef i)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mul_mem_sq_of_smul_eq_zero {A : Subalgebra R (T → R)} (n : R) (hn : ∀ x : omega A, n • x = 0) (x : A)
    (hx : x ∈ augIdeal A) : algebraMap R A n * x ∈ augIdeal A ^ 2 := by
  have h1 : (augIdeal A).toCotangent (algebraMap R A n • (⟨x, hx⟩ : augIdeal A)) = 0 := by
    rw [LinearMap.map_smul, algebraMap_smul]
    exact hn _
  exact (Ideal.toCotangent_eq_zero (augIdeal A) _).1 h1

theorem exists_pow_smul_mem [IsDomain R] [Finite T] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (n : R)
    (hn : ∀ x : omega A, n • x = 0) : ∃ k : ℕ, ∀ f : T → R, n ^ k • f ∈ A := by
  classical
  haveI := Fintype.ofFinite T
  obtain ⟨u, k, hu, huk⟩ := det_trick (augIdeal A) (augIdeal_fg hA) (algebraMap R A n)
    (mul_mem_sq_of_smul_eq_zero n hn)
  have hu1 : (u : T → R) 1 = n ^ k := by
    have h2 : evalAt A 1 (u - algebraMap R A n ^ k) = 0 := huk
    rw [map_sub, map_pow, AlgHom.commutes] at h2
    exact sub_eq_zero.1 h2
  have hut : ∀ t : T, t ≠ 1 → (u : T → R) t = 0 := by
    intro t ht
    obtain ⟨d, hd, hfull⟩ := hA.full
    have hg : (⟨d • Pi.single t (1 : R), hfull _⟩ : A) ∈ augIdeal A := by
      rw [OrderApi.mem_augIdeal]
      simp [Pi.single_apply, ht.symm]
    have h1 := congrFun (congrArg Subtype.val (hu _ hg)) t
    have h2 : (u : T → R) t * d = 0 := by simpa using h1
    exact (mul_eq_zero.1 h2).resolve_right hd
  have hδ : ∀ t : T, n ^ k • (Pi.single t (1 : R) : T → R) ∈ A := by
    intro t
    have h1 := translate_mem hA u.2 t⁻¹
    convert h1 using 1
    ext x
    by_cases hx : x = t
    · subst hx
      simp [hu1]
    · have : t⁻¹ * x ≠ 1 := fun h => hx (by rw [inv_mul_eq_one] at h; exact h.symm)
      simp [Pi.single_apply, hx, hut _ this]
  refine ⟨k, fun f => ?_⟩
  have h1 : n ^ k • f = ∑ t, f t • (n ^ k • (Pi.single t (1 : R) : T → R)) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [h1]
  exact sum_mem fun t _ => A.smul_mem (hδ t) _

end Hopf

section Lat

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {T W : Type} [CommGroup T]

def resMap (toN : W → T) : (T → R) →ₗ[R] (W → Ω) where
  toFun f a := ((f (toN a) : R) : Ω)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isBaseChange_of_sandwich [Fintype W] (L : Submodule R (W → Ω)) (c : R) (hc : (c : Ω) ≠ 0)
    (h1 : ∀ g ∈ L, ∀ a, g a ∈ R) (h2 : ∀ g : W → Ω, (∀ a, g a ∈ R) → (c : Ω) • g ∈ L) :
    IsBaseChange Ω L.subtype := by
  classical
  have hb : ∀ a : W, (c : Ω) • (Pi.single a (1 : Ω) : W → Ω) ∈ L := fun a => h2 _ fun b => by
    by_cases h : b = a
    · subst h; simp [R.one_mem]
    · simp [Pi.single_apply, h, R.zero_mem]
  let bas : W → L := fun a => ⟨_, hb a⟩
  have hsum : ∀ l : L, ∑ a, (⟨(l : W → Ω) a, h1 _ l.2 a⟩ : R) • bas a = c • l := by
    intro l
    apply Subtype.ext
    ext x
    simp [bas, Pi.single_apply, Subalgebra.smul_def, mul_comm]
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  let g' : (W → Ω) →ₗ[Ω] Q := ∑ a, (LinearMap.proj a : (W → Ω) →ₗ[Ω] Ω).smulRight ((c : Ω)⁻¹ • g (bas a))
  have hg' : ∀ h : W → Ω, g' h = ∑ a, h a • ((c : Ω)⁻¹ • g (bas a)) := fun h => by
    simp [g', LinearMap.sum_apply]
  have hgs : ∀ (r : R) (l : L), g (r • l) = (r : Ω) • g l := fun r l => by
    rw [LinearMap.map_smul]
    exact (algebraMap_smul Ω r (g l)).symm
  refine ⟨g', ?_, fun g'' hg'' => ?_⟩
  · ext l
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply]
    rw [hg']
    have h3 : ∀ a, ((l : W → Ω) a) • ((c : Ω)⁻¹ • g (bas a)) =
        (c : Ω)⁻¹ • g ((⟨(l : W → Ω) a, h1 _ l.2 a⟩ : R) • bas a) := by
      intro a
      rw [hgs]
      exact smul_comm _ _ _
    rw [Finset.sum_congr rfl fun a _ => h3 a, ← Finset.smul_sum, ← map_sum, hsum, hgs, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  · apply LinearMap.ext
    intro h
    have h3 : ∀ a, g'' ((c : Ω) • (Pi.single a (1 : Ω) : W → Ω)) = g (bas a) := fun a =>
      LinearMap.congr_fun hg'' (bas a)
    rw [hg']
    have h4 : h = ∑ a, (h a * (c : Ω)⁻¹) • ((c : Ω) • (Pi.single a (1 : Ω) : W → Ω)) := by
      ext x
      simp [Finset.sum_apply, Pi.single_apply, inv_mul_cancel_right₀ hc]
    conv_lhs => rw [h4]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, h3, mul_smul]

theorem lat_clauses [Finite T] [Fintype W] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    (toN : W → T) (fromN : T → W) (hft : ∀ a, fromN (toN a) = a)
    (hst : ∀ f ∈ A, (fun t => f (toN (fromN t))) ∈ A) (c : R) (hc : (c : Ω) ≠ 0)
    (hfull : ∀ f : T → R, c • f ∈ A) (M : AddSubgroup (W → Ω))
    (hM : ∀ g, g ∈ M ↔ ∃ f ∈ A, ∀ a, ((f (toN a) : R) : Ω) = g a) :
    LocFree R (Fintype.card W) M ∧ M ≤ stdLat R W ∧ (∀ h ∈ stdLat R W, (c : Ω) • h ∈ M) ∧
      (1 : W → Ω) ∈ M := by
  classical
  let Ms : Submodule R (W → Ω) := (Subalgebra.toSubmodule A).map (resMap R toN)
  have hMs : ∀ g, g ∈ Ms ↔ g ∈ M := by
    intro g
    rw [hM]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, fun a => rfl⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨f, hf, funext h⟩
  have hle : ∀ g ∈ M, ∀ a, g a ∈ R := by
    intro g hg a
    obtain ⟨f, -, h⟩ := (hM g).1 hg
    rw [← h a]
    exact (f (toN a)).2
  have h3 : ∀ h : W → Ω, (∀ a, h a ∈ R) → (c : Ω) • h ∈ M := by
    intro h hh
    refine (hM _).2 ⟨c • fun t => ⟨h (fromN t), hh _⟩, hfull _, fun a => ?_⟩
    simp [hft, Subalgebra.smul_def]
  have hpm : ∀ g, g ∈ stdLat R W ↔ ∀ a, g a ∈ R := by
    intro g
    simp [stdLat, AddSubgroup.mem_pi]
  refine ⟨?_, fun g hg => (hpm g).2 (hle g hg), fun h hh => h3 h ((hpm h).1 hh),
    (hM _).2 ⟨1, A.one_mem, fun a => rfl⟩⟩
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Finite R (Subalgebra.toSubmodule A) := hA.finite
  have hfin : Module.Finite R Ms := Module.Finite.map _ _
  let s : A →ₗ[R] Ms := ((resMap R toN).comp A.val.toLinearMap).codRestrict Ms fun f => ⟨f.1, f.2, rfl⟩
  have hi : ∀ g : Ms, (fun t => (⟨(g : W → Ω) (fromN t), hle _ ((hMs _).1 g.2) _⟩ : R)) ∈ A := by
    rintro ⟨g, hg⟩
    obtain ⟨f, hf, h⟩ := (hM g).1 ((hMs g).1 hg)
    convert hst f hf using 1
    ext t
    simp [h]
  let i : Ms →ₗ[R] A :=
    { toFun := fun g => ⟨_, hi g⟩
      map_add' := fun _ _ => by
        apply Subtype.ext; ext t; rfl
      map_smul' := fun _ _ => by
        apply Subtype.ext; ext t; rfl }
  have hsi : s.comp i = LinearMap.id := by
    ext g a
    simp [s, i, resMap, hft]
  have hproj : Module.Projective R Ms := Module.Projective.of_split i s hsi
  have hbc : IsBaseChange Ω Ms.subtype := isBaseChange_of_sandwich R Ms c hc
    (fun g hg => hle g ((hMs g).1 hg)) fun g hg => (hMs _).2 (h3 g hg)
  have := LocFreeProj.locFree_of_projective R (Fintype.card W) Ms hfin hproj
    (Module.finrank_fintype_fun_eq_card Ω) hbc
  have hMeq : Ms.toAddSubgroup = M := by
    ext g
    exact hMs g
  rwa [hMeq] at this

end Lat

section Th

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {T W : Type} [CommGroup T]
  [AddCommGroup W] {A : Subalgebra R (T → R)} {L : Type} [AddCommGroup L] [Module R L] {r : ℕ}

theorem mem_dotDual_iff (Λ : AddSubgroup (Fin r → Ω)) (m : Fin r → Ω) :
    m ∈ dotDual R Λ ↔ ∀ l ∈ Λ, l ⬝ᵥ m ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem th_clauses {C : Type} [AddCommGroup C] [Module R C] (toN : W → T) (fromN : T → W) (h1 : fromN 1 = 0) (h0 : toN 0 = 1)
    (hft : ∀ a, fromN (toN a) = a) (hst : ∀ f ∈ A, (fun t => f (toN (fromN t))) ∈ A)
    (M : AddSubgroup (W → Ω)) (hM : ∀ g, g ∈ M ↔ ∃ f ∈ A, ∀ a, ((f (toN a) : R) : Ω) = g a)
    (hMR : ∀ a ∈ R, ∀ g ∈ M, a • g ∈ M)
    (I : Submodule R (T → R)) (hI : ∀ f, f ∈ I ↔ f ∈ A ∧ f 1 = 0) (cl : I →ₗ[R] C)
    (θ : Module.Dual R L →ₗ[R] C) (hsurj : Function.Surjective θ)
    (Der : (T → R) → Module.Dual R L → Prop)
    (hDer : ∀ (f : I) (w : Module.Dual R L), θ w = cl f ↔ Der f.1 w)
    (N : ℕ) (hker : ∀ w, θ w = 0 ↔ ∃ u, w = N • u)
    (ev : Module.Dual R L →ₗ[R] (Fin r → Ω)) (Λ : AddSubgroup (Fin r → Ω))
    (H1 : ∀ u, ev u ∈ dotDual R Λ)
    (H2 : ∀ m ∈ dotDual R Λ, ∃ u, ev u = m ∧ ∃ f : I,
      (∀ t, f.1 (toN (fromN t)) = f.1 t) ∧ θ u = cl f)
    (Th : AddSubgroup ((W → Ω) × (Fin r → Ω)))
    (hTh : Th = AddSubgroup.closure {z | z.1 ∈ M ∧ z.1 0 = 0 ∧ ∃ (f : T → R) (u : Module.Dual R L),
      (∀ t, ((f t : R) : Ω) = z.1 (fromN t)) ∧ Der f u ∧ ∀ k, z.2 k = ev u k}) :
    (∀ a ∈ R, ∀ v ∈ Th, a • v ∈ Th) ∧ (∀ g, (∃ m, (g, m) ∈ Th) ↔ g ∈ M ∧ g 0 = 0) ∧
      (∀ m, (∃ g, (g, m) ∈ Th) ↔ m ∈ dotDual R Λ) ∧
      ∀ m, (0, m) ∈ Th ↔ m ∈ mulLat (N : Ω) (dotDual R Λ) := by
  have haug : ∀ g ∈ M, g 0 = 0 → ∃ f : I, ∀ t, ((f.1 t : R) : Ω) = g (fromN t) := by
    intro g hg hg0
    obtain ⟨f₀, hf₀, h⟩ := (hM g).1 hg
    have hz : (fun t => f₀ (toN (fromN t))) 1 = 0 := by
      apply Subtype.ext
      simp only [h1]
      simpa using (h 0).trans hg0
    exact ⟨⟨_, (hI _).2 ⟨hst f₀ hf₀, hz⟩⟩, fun t => h _⟩
  let S : ((W → Ω) × (Fin r → Ω)) → Prop := fun z => z.1 ∈ M ∧ z.1 0 = 0 ∧ ∃ (f : I)
    (u : Module.Dual R L), (∀ t, ((f.1 t : R) : Ω) = z.1 (fromN t)) ∧ θ u = cl f ∧ z.2 = ev u
  have hSTh : ∀ z, S z → z ∈ Th := by
    rintro z ⟨hz, hz0, f, u, hf, hu, hev⟩
    rw [hTh]
    exact AddSubgroup.subset_closure ⟨hz, hz0, f.1, u, hf, (hDer f u).1 hu, fun k => by rw [hev]⟩
  have hThS : ∀ z ∈ Th, S z := by
    intro z hz
    rw [hTh] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z h =>
      obtain ⟨hz, hz0, f, u, hf, hd, hev⟩ := h
      obtain ⟨f', hf'⟩ := haug _ hz hz0
      have hff : f'.1 = f := funext fun t => Subtype.ext ((hf' t).trans (hf t).symm)
      refine ⟨hz, hz0, f', u, hf', (hDer f' u).2 (hff ▸ hd), funext hev⟩
    | zero =>
      exact ⟨M.zero_mem, rfl, 0, 0, fun t => rfl, by simp, by simp⟩
    | add z z' _ _ h h' =>
      obtain ⟨hz, hz0, f, u, hf, hu, hev⟩ := h
      obtain ⟨hz', hz0', f', u', hf', hu', hev'⟩ := h'
      refine ⟨M.add_mem hz hz', by simp [hz0, hz0'], f + f', u + u', fun t => ?_, ?_, ?_⟩
      · have h3 := hf t
        have h4 := hf' t
        simp only [Submodule.coe_add, Pi.add_apply, Prod.fst_add, Subalgebra.coe_add, h3, h4]
      · rw [map_add, map_add, hu, hu']
      · simp [hev, hev']
    | neg z _ h =>
      obtain ⟨hz, hz0, f, u, hf, hu, hev⟩ := h
      refine ⟨M.neg_mem hz, by simp [hz0], -f, -u, fun t => ?_, ?_, ?_⟩
      · have h3 := hf t
        simp only [Submodule.coe_neg, Pi.neg_apply, Prod.fst_neg, Subalgebra.coe_neg, h3]
      · rw [map_neg, map_neg, hu]
      · simp [hev]
  refine ⟨fun a ha v hv => ?_, fun g => ⟨?_, ?_⟩, fun m => ⟨?_, ?_⟩, fun m => ⟨?_, ?_⟩⟩
  · obtain ⟨hz, hz0, f, u, hf, hu, hev⟩ := hThS v hv
    let a' : R := ⟨a, ha⟩
    refine hSTh _ ⟨hMR a ha _ hz, by simp [hz0], a' • f, a' • u, fun t => ?_, ?_, ?_⟩
    · have h3 := hf t
      change a * ((f.1 t : R) : Ω) = a * v.1 (fromN t)
      rw [h3]
    · rw [map_smul, hu, map_smul]
    · simp only [Prod.smul_snd, hev, map_smul]
      rfl
  · rintro ⟨m, hm⟩
    obtain ⟨hz, hz0, -⟩ := hThS _ hm
    exact ⟨hz, hz0⟩
  · rintro ⟨hg, hg0⟩
    obtain ⟨f, hf⟩ := haug g hg hg0
    obtain ⟨u, hu⟩ := hsurj (cl f)
    exact ⟨ev u, hSTh _ ⟨hg, hg0, f, u, hf, hu, rfl⟩⟩
  · rintro ⟨g, hg⟩
    obtain ⟨-, -, f, u, -, -, hev⟩ := hThS _ hg
    change m = _ at hev
    rw [hev]
    exact H1 u
  · intro hm
    obtain ⟨u, hu, f, hf, hθ⟩ := H2 m hm
    have hfI := (hI _).1 f.2
    refine ⟨fun a => ((f.1 (toN a) : R) : Ω), hSTh _ ⟨(hM _).2 ⟨_, hfI.1, fun a => rfl⟩, ?_, f, u,
      fun t => ?_, hθ, hu.symm⟩⟩
    · simp [h0, hfI.2]
    · simp [hf]
  · intro hm
    obtain ⟨-, -, f, u, hf, hu, hev⟩ := hThS _ hm
    have hf0 : f = 0 := by
      apply Subtype.ext
      ext t
      simpa using hf t
    rw [hf0, map_zero] at hu
    obtain ⟨u', rfl⟩ := (hker u).1 hu
    refine ⟨ev u', H1 u', ?_⟩
    change (N : Ω) • ev u' = m
    rw [show m = ev (N • u') from hev, map_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨m', hm', rfl⟩
    obtain ⟨u', hu', -⟩ := H2 m' hm'
    refine hSTh _ ⟨M.zero_mem, rfl, 0, N • u', fun t => rfl, ?_, ?_⟩
    · rw [map_zero]
      exact (hker _).2 ⟨u', rfl⟩
    · change (N : Ω) • m' = _
      rw [map_nsmul, hu', Nat.cast_smul_eq_nsmul]

end Th

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg
